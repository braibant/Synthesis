Add Rec LoadPath "./" as Synthesis. 
Require Import Common.
Require Import DList.
Require Import Core. 
Require Word Vector. 


(** * Definition of [expr] and [action] *)

(** In order to factorise a bit development, we do not have exactly
the same definition as the one in the paper, where each primitive is
inlined in the following action data-type. Instead, with have a
dependently typed notion of primitive, that encapsulates interaction
with the external state. The paper corresponds to a version of the
[action] definiton where [primitive] is inlined. *)

Inductive primitive (Phi : state) : list type -> type -> Type:=
| input_read : forall t, var Phi (Tinput t) -> primitive Phi nil t
(* register operations *)
| register_read : forall t, var Phi (Treg t) ->  primitive Phi nil t
| register_write : forall t, var Phi (Treg t) -> primitive Phi (t:: nil) Tunit
(* register file primitives *)
| regfile_read : forall n t (v : var Phi (Tregfile n t)), primitive Phi ([ (Tint n)])%list  t
| regfile_write : forall n t (v : var Phi (Tregfile n t)), primitive Phi ([ (Tint n); t])%list  Tunit.

Section s.
  
  Variable Phi : state.

  Section t. 
    Variable Var : type -> Type. 
    Inductive expr :  type -> Type :=
    | Evar : forall t (v : Var t), expr t
    | Eandb : expr B -> expr B -> expr B
    | Eorb  : expr B -> expr B -> expr B
    | Exorb : expr B -> expr B -> expr B
    | Enegb : expr B -> expr B

    (* "type-class" *)
    | Eeq   : forall t, expr t -> expr t -> expr B

    (* integer operations *)                                          
    | Elt   : forall n, expr (Int n) -> expr (Int n) -> expr B
    | Ele   : forall n, expr (Int n) -> expr (Int n) -> expr B
    | Eadd  : forall n, expr (Int n) -> expr (Int n) -> expr (Int n)
    | Esub  : forall n, expr (Int n) -> expr (Int n) -> expr (Int n)
    | Elow  : forall n m, expr (Int (n + m)) -> expr (Int n)
    | Ehigh  : forall n m, expr (Int (n + m)) -> expr (Int m)
    | EcombineLH   : forall n m, expr (Int n) -> expr (Int m) -> expr (Int (n + m))

    | Econstant : forall  ty (c : constant ty), expr ( ty)
                          
    | Emux : forall t, expr B -> expr t -> expr t -> expr t 

    (* Tuple operations *)
    | Efst : forall l t , expr (Ttuple (t::l)) -> expr t
    | Esnd : forall l t , expr (Ttuple (t::l)) -> expr (Ttuple l)
    | Enth : forall l t (m : var l t), expr (Ttuple l) -> expr t
    | Etuple : forall l (exprs : DList.T (expr) l), expr (Ttuple l). 

    
    Inductive action : type -> Type :=
    | Return : forall t (exp : expr t), action t
    | Bind :
      forall t u 
        (a : action  t) 
        (f : Var t -> action u),  
        action u
    | Assert : forall (e : expr B), action Tunit
    | Primitive : 
      forall args res (p : primitive Phi args res)
        (exprs : DList.T (expr) args),
        action res 
    | OrElse : forall t, action t -> action t -> action t.
  End t. 

  Definition Action t := forall Var, action Var t.
  Definition Expr t := forall Var, expr Var t. 

  Fixpoint eval_expr (t : type) (e : expr eval_type t) : eval_type t :=
    match e with
      | Evar t v => v
      | Eandb a b => andb (eval_expr _ a) (eval_expr _ b)
      | Eorb a b => orb (eval_expr _ a) (eval_expr _ b)
      | Exorb a b => xorb (eval_expr _ a) (eval_expr _ b)
      | Enegb a => negb (eval_expr _ a) 

      (* "type-class" *)
      | Eeq t a b => type_eq t (eval_expr t a) (eval_expr t b)
                            
      (* integer operations *)                                          
      | Elt n a b => @Word.lt n (eval_expr _ a) (eval_expr _ b)
      | Ele n a b => @Word.le n (eval_expr _ a) (eval_expr _ b)
      | Eadd n a b => @Word.add n (eval_expr _ a) (eval_expr _ b)
      | Esub n a b => @Word.sub n (eval_expr _ a) (eval_expr _ b)
      | Elow n m a => @Word.low n m (eval_expr _ a) 
      | Ehigh n m a => @Word.high n m (eval_expr _ a)
      | EcombineLH n m a b => @Word.combineLH n m (eval_expr _ a) (eval_expr _ b)
      | Emux t b x y => if eval_expr _ b then eval_expr t x else eval_expr t y
      | Econstant ty c => c
      | Etuple l exprs => 
          DList.to_tuple eval_expr exprs
      | Enth l t v e => 
          Tuple.get l t v (eval_expr (Ttuple l) e)
      | Efst l t  e => 
          Tuple.fst  (eval_expr _ e)
      | Esnd l t  e => 
          Tuple.snd  (eval_expr _ e)
    end. 
End s. 

Delimit Scope expr_scope with expr. 
Delimit Scope action_scope with action. 

Arguments expr Var _%list. 
Arguments action _%list _ _. 

(** * Notations for actions and expressions  *)

Arguments Bind {Phi Var t u} _%action _%action. 
Arguments Return {Phi Var t} _%expr. 

Definition Bind' {Phi Var t u} a (f : expr Var t -> action Phi Var u) :=  
    Bind (a) (fun x => let x := Evar _ _ x in f x).  

(** A notation for the general bind, with [a] being an action  *)
Notation "'do' x <- a ; b" := (Bind' a (fun x =>  b)) 
                               (at level 200, x ident, a at level 100, b at level 200) 
                          : action_scope. 

(** A notation for the general bind, when the right hand side is an expression  *)
Notation "'do' x <~ a ; b " := (Bind' (Return a) (fun x =>  b)) 
                                (at level 200, x ident, a at level 100, b at level 200) 
                              : action_scope. 

Notation "'ret' x" := (Return x) (at level 0) : action_scope .   

Arguments Assert {Phi Var} e%expr. 

Definition When {Phi Var t} e a : action Phi Var t := @Bind Phi Var _ _ (Assert e) (fun _ => a). 
Arguments When {Phi Var t} _%expr _%action. 
Notation " 'when' e 'do' B" := (When e B) (at level 200, e at level 100, B at level 200). 

Arguments Primitive {Phi Var} args res _ _%expr. 

(** ** Primitives *)
Arguments register_read {Phi t} _. 
Notation "'read' [: v ]" := (Primitive nil _ (register_read v) DList.nil) (no associativity).
Notation "! v" := (Primitive nil _ (register_read v) DList.nil ) (no associativity, at level 71). 

Arguments register_write {Phi t} _. 
Notation "'write' [: v <- w ]" := (Primitive (cons _ nil) Tunit (register_write v) (DList.cons (w)%expr (DList.nil))) (no associativity). 
Notation "v ::= w" := (Primitive (cons _ nil) Tunit (register_write v) (DList.cons (w)%expr (DList.nil))) (no associativity, at level 71). 

Arguments regfile_read {Phi n t} _. 
Notation "'read' M [: v ]" := (Primitive ([ (_)])%list _ (regfile_read M ) (DList.cons (v)%expr (DList.nil))) (no associativity). 

Arguments regfile_write {Phi n t} _ . 
Notation "'write' M [: x <- v ]" := (Primitive ([ (_); _])%list _ (regfile_write M ) (DList.cons (x)%expr (DList.cons (v)%expr (DList.nil)))) (no associativity). 

(** ** Expressions  *)
Arguments Enth  {Var l t} m _%expr. 
Arguments Evar  {Var t} _. 

Notation "~ x" :=  (Enegb _  x)%expr : expr_scope. 
Notation "a || b" := (Eorb _ a b)%expr : expr_scope. 
Notation "a && b" := (Eandb _ a b)%expr : expr_scope. 
Notation "a - b" := (Esub _ _ a b)%expr : expr_scope. 
Notation "a + b" := (Eadd _ _ a b)%expr : expr_scope. 
Notation "a = b" := (Eeq _ _ a b)%expr : expr_scope. 
Notation "a < b" := (Elt _ _ a b)%expr : expr_scope. 
Notation "x <= y" := (Ele _ _ x y)%expr : expr_scope. 
Notation "x <> y" := (~(x = y))%expr : expr_scope. 
Notation low x := (Elow _ _ _ x).
Notation high x := (Ehigh _ _ _ x).  
Notation combineLH x y := (EcombineLH _ _ _ x y). 

Arguments Econstant {Var ty} _.  
Notation "#i x" := (Econstant (Cword x)) (at level 0). 
Notation "#b x" := (Econstant (Cbool x)) (at level 0). 
Notation "#" := Econstant. 

Definition Ctt : constant Tunit := tt. 
    
Arguments Efst {Var l t} _%expr. 
Arguments Esnd {Var l t} _%expr. 

Arguments Emux {Var t} _%expr _%expr _%expr. 
Notation "b ? l : r" := (Emux b l r) (at level 200, l, r at level 200).  

Notation apply x f := (f x) (only parsing). 

(* A do-notation for tuple-expressions *)
Definition Asplit {Phi Var l t u}  f (a: expr Var (Ttuple (t::l))) : action Phi Var u:= 
  (do x <- ret (Efst a);
   do y <- ret (Esnd a);
   f x y)%action. 
    
Notation "'do' ( x , .. , y ) <~ a ; b" :=
(apply a (Asplit (fun x => .. ( Asplit (fun y _ => b)) .. ))) (at level 200, x closed binder, a at level 100, b at level 200): action_scope.  


Arguments Etuple {Var l} _%dlist. 
Notation "[ 'tuple' x , .. , y ]" := (Etuple (x :: .. (y :: [ :: ]) .. )%dlist) (only parsing): expr_scope. 
(**
 Unfortunately, this notation cannot be defined due to a bug... It redefines the notation for the pairs in every scope 
 Notation "( x , .. , z )" := (Etuple (x :: .. (z :: [ :: ]) .. )%dlist) (at level 0): expr_scope. 
*)



(** * Semantics of Fe-Si *)
Module Diff. 
  Section t. 
    Variable Phi : state. 
    Definition T := DList.T (option ∘ eval_mem) Phi. 
    (* first *)
    Definition add (Delta : T) t (v : var Phi t) w :  T :=
      match DList.get v Delta  with 
        | None =>  (DList.set v (Some w) Delta)
        | Some x => Delta
      end.
    
  End t. 
  
  Definition init (Phi : state ): T Phi := DList.init (fun _ => None) Phi. 
  
  Fixpoint apply (Phi : state) : T Phi -> DList.T eval_mem Phi -> DList.T eval_mem Phi :=
    match Phi with
      | nil => fun _ _ => [ :: ]
      | cons t Phi => fun Delta E =>
                     match DList.hd Delta with
                       | None => (DList.hd E :: apply Phi (DList.tl Delta) (DList.tl E))
                       | Some d => d :: apply Phi (DList.tl Delta) (DList.tl E)
                     end
    end%dlist.
  
End Diff. 


Module Sem. 

  
  
  Module Dyn. 
    (** dynamic semantics: 
    - continuation passing style: the current diff is threaded through the execution 
    - illegal behaviors are denoted by None *)
    Section t. 
      Variable Phi : state. 
      (* semantics :  Action Phi t -> T t  *)
      
      Definition T t := eval_state Phi -> Diff.T Phi -> option (t * Diff.T Phi). 

      Definition Return {t} (e : t) : T t  := fun st d => Some (e, d).

      Definition Bind {s t} : T s -> (s -> T t) -> T t :=
        fun (x : T s) (f : s -> T t) (st : eval_state Phi) (d : Diff.T Phi) => 
          match x st d with 
              Some (e, d') =>  f e st d' 
            | None => None
          end. 

      Definition Retry {t} : T t := fun _ _ => None. 

      Definition OrElse {t} : T t -> T t -> T t :=
        fun a b st Delta => match a st Delta with 
                         | None => b st Delta
                         | Some Delta => Some Delta
                       end. 
                                                
        
      Definition primitive_denote  args res (p : primitive Phi args res) (exprs : DList.T eval_type args) : T (eval_type res). 
      refine (match
          p in (primitive _ l t) return (DList.T eval_type l -> T (eval_type t))
        with
          | input_read t v => 
            fun _ (st: eval_state Phi) Delta => 
            Some (DList.get v st, Delta)
          | register_read t v =>
              fun _ (st : eval_state Phi)
                  (Delta : Diff.T Phi) => Some (DList.get v st, Delta)
          | register_write t v =>
              fun (exprs : DList.T eval_type [t]) (_ : eval_state Phi) (Delta : Diff.T Phi) =>
                let w := DList.hd exprs in 
                  Some (tt, Diff.add Phi Delta (Treg t) v w)
          | regfile_read n t v  =>
              fun (exprs : DList.T eval_type [ (Tint n)]) 
                  (st : eval_state Phi) (Delta : Diff.T Phi) =>
                let rf := DList.get  v st in
                let adr := DList.hd exprs in
                let v := Regfile.get rf (adr) in Some (v, Delta)
          | regfile_write n t v =>
              fun (exprs : DList.T eval_type [ (Tint n); t]) 
                  (st : eval_state Phi) (Delta : Diff.T Phi) =>
                let rf := DList.get  v st in
                let (adr, w) := (DList.hd exprs, DList.hd (DList.tl exprs)) in
                let rf :=  Regfile.set rf adr w                         
                in
                  Some (tt, Diff.add Phi Delta (Tregfile n t) v rf)
        end exprs). 
      Defined. 
    End t. 
  End Dyn. 

  (** dynamic semantics: 
    - all guard failures are represented by None. 
    - continuation passing style: the current diff is threaded through the execution 
  *)
  Section t. 
    Variable Phi : state. 
    Fixpoint eval_action (t : type) (a : action Phi eval_type t) : 
      (Dyn.T Phi (eval_type t)) :=
      match a with
        | Return t exp => Dyn.Return Phi (eval_expr _ exp)
        | Bind t u a f => 
            let act := eval_action _ a in 
              let f' := (fun e => eval_action u (f e)) in 
                Dyn.Bind Phi act f'              
        | Assert e => 
            let g := eval_expr _ e in 
              match g with 
                | true => Dyn.Return Phi tt
                | false => Dyn.Retry  Phi
              end
        | Primitive args res p exprs => 
            Dyn.primitive_denote Phi args res p (DList.map eval_expr  exprs)
        | OrElse t a b => Dyn.OrElse Phi (eval_action _ a) (eval_action _ b)  
      end.                 
    
  End t. 
  Arguments eval_action {Phi} {t} _%action _ _.  

End Sem.           

Definition Eval Phi (st: eval_state Phi)  t (A : Action Phi t ) Delta :=  @Sem.eval_action Phi t (A _) st Delta. 

(** The next-step function computes what should be the next state of a
circuit. 


TODO: remark that Diff.init initialize even the Inputs with None,
which is not wrong, but prevents us from reasonning about circuits
that depend on their inputs. *)

Definition Next {t} Phi st (A : Action Phi t)  : option (eval_type t * eval_state Phi ):= 
  let Delta := Eval Phi st _ A (Diff.init Phi) in 
    match Delta with 
      | None => None 
      | Some Delta => Some (fst Delta, Diff.apply Phi (snd Delta) st)
    end. 

(** We define two functions that computes the output of a circuit --
without internal state.  *)

Definition output  (t : type) (A : action nil eval_type t) : 
    option (eval_type t) :=    
    match Sem.eval_action  A DList.DList.nil (Diff.init []%list)  with
      | Some p => Some (fst p)
      | None => None
    end. 

Definition Output (t : type) (A : Action nil t) := output t (A eval_type).


Module Close. 
  Section t.
  (** * Closing a circuit.  

      Circuits are oftne manipulated in an "open" fashion, using
      variables instead of inputs. The function [internalize] takes as
      input a circuit generator of type [Var t -> action Phi u], and
      produces a circuit of type [action (Phi :: Tinput t) u], with the
      variable being replaced by a formal input
   *) 
  Variable Var : type -> Type.

  Definition primitive_generalize args res l1 (p : primitive l1 args res) l2:
    primitive (List.app  l1 l2) args res :=
    match p with
      | input_read t x => input_read _ _  (var_lift x )
      | register_read t x => register_read (var_lift x)
      | register_write t x => register_write (var_lift x)
      | regfile_read n t v => regfile_read  (var_lift v)
      | regfile_write n t v => regfile_write (var_lift v)
    end.
      
  Definition generalize (l1 : list mem) T (a : action l1 Var T) : forall l2, action (List.app l1 l2) Var T. 
  refine (let fix aux (l1 : list mem) T (a : action l1 Var T) :
                  forall l2, action (List.app l1 l2) Var T :=
                match a  with
                  | Return t exp => fun l2 => Return (exp)
                  | Bind t u a f => fun l2 => let a' := aux _ _ a l2 in Bind a' (fun x => aux _ _ (f x) _)
                  | Assert e => fun l2 => Assert e
                  | Primitive args res p exprs => fun l2 : list mem =>
                                                   Primitive args res 
                                                             (primitive_generalize args res _ p l2)
                                                             exprs
                  | OrElse t b1 b2 => fun l2 => OrElse _ _ t (aux _ _ b1 l2) (aux _ _ b2 l2)
                end
            in aux l1 T a
           ).
  Defined. 

  Fixpoint var_last {A} (l : list A) (t : A) : var (List.app l [t]) t :=
    match l with 
      | nil => var_0
      | hd :: q => var_S (var_last q t)
      end%list. 
  
  Definition internalize {Phi T U} (c : Var T -> action Phi Var U) : 
    action (List.app Phi [Tinput T]) Var U :=
    let v := (var_last Phi (Tinput T)) in 
    (Bind  (Primitive nil T  (input_read (List.app Phi [Tinput T]) T  v) DList.DList.nil) (fun x => 
      generalize _ _ (c x) _))%action.
  End t. 
End Close.
  
Definition Close := Close.internalize. 
