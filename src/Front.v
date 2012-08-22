Require Import Common.
Require Import DList.
Require Import Core. 
Require Word Array. 

Inductive primitive (Phi : state) : list type -> type -> Type:=
| register_read : forall t, var Phi (Treg t) ->  primitive Phi nil t
| register_write : forall t, var Phi (Treg t) -> primitive Phi (t:: nil) Tunit
(* register file primitives *)
| regfile_read : forall n t (v : var Phi (Tregfile n t)), primitive Phi ([ (Tint n)])%list  t
| regfile_write : forall n t (v : var Phi (Tregfile n t)), primitive Phi ([ (Tint n); t])%list  Tunit
(* fifos primitives *).

Section s.
  
  Variable Phi : state.

  Section t. 
    Variable Var : type -> Type. 
    Inductive expr :  type -> Type :=
    | Evar : forall t (v : Var t), expr t
    | Ebuiltin : forall args res (f : builtin args res), 
                   DList.T  expr (args) -> 
                   expr  ( res)
    | Econstant : forall  ty (c : constant ty), expr ( ty)
                          
    | Emux : forall t, expr Tbool -> expr t -> expr t -> expr t 

    (* Tuple operations *)
    | Efst : forall l t , expr (Ttuple (t::l)) -> expr t
    | Esnd : forall l t , expr (Ttuple (t::l)) -> expr (Ttuple l)
    | Enth : forall l t (m : var l t), expr (Ttuple l) -> expr t
    | Etuple : forall l (exprs : DList.T (expr) l), expr (Ttuple l). 
    
    
    Section induction. 
      (** Since the induction principle that is generated is not
      useful, we have to define our own.  *)

      Variable P : forall t : type, expr t -> Prop.  
      Hypothesis Hvar : forall (t : type) (v : Var t), P t (Evar t v). 
      Hypothesis Hbuiltin : 
      forall (args : list type) (res : type) (f0 : builtin args res)
        (t : DList.T expr args), 
        (* (forall t (e : expr t), P t e) -> *)
        DList.Forall P t ->
        P res (Ebuiltin args res f0 t). 
      Hypothesis Hconstant : 
      forall (ty : type) (c : constant ty), P ty (Econstant ty c). 
      Hypothesis Hmux : forall (t : type) (e : expr B) (l r : expr t),
                          P B e -> P t l -> P t r ->  P t (Emux t e l r ).  
      Hypothesis Hfst : forall (l : list type) (t : type) (e : expr (Ttuple (t :: l))),
        P (Ttuple (t :: l)) e -> P t (Efst l t e).  
      Hypothesis Hsnd : forall (l : list type) (t : type) (e : expr (Ttuple (t :: l))),
        P (Ttuple (t :: l)) e -> P (Ttuple l) (Esnd l t e). 
      Hypotheses Hnth : forall (l : list type) (t : type) (m : var l t) (e : expr (Ttuple l)),
        P (Ttuple l) e -> P t (Enth l t m e). 
      Hypothesis Htuple : forall (l : list type) (exprs : DList.T expr l),
                            DList.Forall P exprs -> 
                            P (Ttuple l) (Etuple l exprs). 
      
      Lemma expr_ind_alt (t : type) (e : expr t) :  P t e. 
      refine (let fix fold (t : type) (e : expr t) :  P t e  := 
                  match e with
                    | Evar t v => Hvar t v
                    | Ebuiltin args res f x =>  Hbuiltin args res f _ _
                    | Econstant ty c => Hconstant ty c
                    | Emux t x x0 x1 => Hmux t x x0 x1 (fold _ x) (fold _ x0) (fold _ x1)
                    | Efst l t x => Hfst l t x (fold _ x)
                    | Esnd l t x => Hsnd l t x (fold _ x) 
                    | Enth l t m x => Hnth l t m x (fold _ x)
                    | Etuple l exprs => Htuple l exprs _  end in fold t e);
        clear Hbuiltin Hvar Hconstant Hmux Hfst Hsnd Hnth Htuple.
      {
        clear f.
        induction x. simpl; apply I.
        split; [apply fold | apply IHx]; auto.      
      }
      {
        induction exprs. simpl; apply I. 
        split; [apply fold | apply IHexprs]; auto.
      }
      Qed. 
    End induction. 

    Inductive action : type -> Type :=
    | Return : forall t (exp : expr t), action t
    | Bind :
      forall t u 
        (a : action  t) 
        (f : Var t -> action u),  
        action u
    | Assert : forall (e : expr Tbool), action Tunit
    | Primitive : 
      forall args res (p : primitive Phi args res)
        (exprs : DList.T (expr) args),
        action res 
    | OrElse : forall t, action t -> action t -> action t.
  End t. 

  Definition Action t := forall Var, action Var t.
  Definition Expr t := forall Var, expr Var t. 

  Notation eval_type_list := (ETuple.of_list eval_type). 
  
  Fixpoint eval_expr (t : type) (e : expr eval_type t) : eval_type t :=
    match e with
      | Evar t v => v
      | Ebuiltin args res f exprs => 
          let exprs := 
              DList.to_tuple eval_expr  exprs
          in
            builtin_denotation args res f exprs                            
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

(** * Actions *)

Arguments Bind {Phi Var t u} _%action _%action. 
Arguments Return {Phi Var t} _%expr. 

Definition Bind' {Phi Var t u} a (f : expr Var t -> action Phi Var u) :=  
    Bind (a) (fun x => let x := Evar _ _ x in f x).  

(** A notation for the general bind, with [a] being an action  *)
Notation "'do' x <- a ; b" := (Bind' a (fun x =>  b)) 
                               (at level 200, x ident, a at level 100, b at level 200) 
                          : action_scope. 

Notation "a ;; b" := (Bind a (fun _ => b)) 
                            (at level 200,  b at level 200) 
                          : action_scope. 

Notation "'do' x <~ a ; b " := (Bind' (Return a) (fun x =>  b)) 
                                (at level 200, x ident, a at level 100, b at level 200) 
                              : action_scope. 

(* (** Another notation to bind expressions  *) *)
(* Notation "'do' x <- e ; b" := (Bind' (Return e) (fun x => b))  *)
(*                                (at level 200, x ident, e at level 100, b at level 200)  *)
(*                              : action_scope.  *)
  
Notation "'ret' x" := (Return x) (at level 0) : action_scope .   

(** old style binding, deprecated  *)
Notation "'DO' X <- A ; B" := (Bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200) : action_scope. 

Arguments Assert {Phi Var} e%expr. 

Definition When {Phi Var t} e a : action Phi Var t := @Bind Phi Var _ _ (Assert e) (fun _ => a). 
Arguments When {Phi Var t} _%expr _%action. 
Notation " 'WHEN' e ; B" := (When e B) (at level 200, e at level 100, B at level 200). 
Notation " 'when' e 'do' B" := (When e B) (at level 200, e at level 100, B at level 200). 

Arguments Primitive {Phi Var} args res _ _%expr. 

(** * Primitives *)
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

(** * Expressions  *)
Arguments Enth  {Var l t} m _%expr. 
Arguments Evar  {Var t} _. 

Arguments Ebuiltin {Var} {args res} _ _%dlist. 
Notation "{< f ; x ; y ; z >}" := (Ebuiltin f [ :: x ; y ; z]) : expr_scope. 
Notation "{< f ; x ; y >}" := (Ebuiltin f [ :: x ; y]) : expr_scope. 
Notation "{< f ; x >}" := (Ebuiltin f [ :: x]) : expr_scope. 

Notation "~ x" :=  ({< BI_negb ; x >})%expr : expr_scope. 
Notation "a || b" := ({< BI_orb ; a ; b >})%expr : expr_scope. 
Notation "a && b" := ({< BI_andb ; a ; b >})%expr : expr_scope. 
Notation "a - b" := ({< BI_minus _ ; a ; b >})%expr : expr_scope. 
Notation "a + b" := ({< BI_plus _ ; a ; b >})%expr : expr_scope. 
Notation "a = b" := ({< BI_eq _ ; a ; b >})%expr : expr_scope. 
Notation "a < b" := ({< BI_lt _ ; a ; b >})%expr : expr_scope. 
Notation "x <= y" := ((x < y) || (x = y))%expr : expr_scope. 
Notation "x <> y" := (~(x = y))%expr : expr_scope. 
Notation low x := ( Ebuiltin (BI_low _ _) ([ :: x])%dlist). 
Notation high x := ( Ebuiltin (BI_high _ _) ([ :: x])%dlist). 
Notation combineLH x y := ( Ebuiltin  (BI_combineLH _ _) [ :: x ; y ]). 

Arguments Econstant {Var ty} _.  
Notation "#i x" := (Econstant (Cword x)) (at level 0). 
Notation "#b x" := (Econstant (Cbool x)) (at level 0). 
Notation "#" := Econstant. 

Definition Ctt : constant Tunit := tt. 
    
Arguments Efst {Var l t} _%expr. 
Arguments Esnd {Var l t} _%expr. 

Arguments Emux {Var t} _%expr _%expr _%expr. 
Notation "b ? l : r" := (Emux b l r) (at level 200, l, r at level 200).  

Definition Asplit {Phi Var l t u}  f (a: expr Var (Ttuple (t::l))) : action Phi Var u:= 
  (do x <- ret (Efst a);
   do y <- ret (Esnd a);
   f x y)%action. 
    
Notation apply x f := (f x) (only parsing). 

Notation "'do' ( x , .. , y ) <- a ; b" :=
(apply a (Asplit (fun x => .. ( Asplit (fun y _ => b)) .. ))) (at level 200, x closed binder, a at level 100, b at level 200): action_scope.  

Arguments Etuple {Var l} _%dlist. 
Notation "[ 'tuple' x , .. , y ]" := (Etuple (x :: .. (y :: [ :: ]) .. )%dlist) : expr_scope. 

Module Diff. 
  Section t. 
    Variable Phi : state. 
    Definition T := DList.T (option ∘ eval_sync) Phi. 
    (* first *)
    Definition add (Delta : T) t (v : var Phi t) w :  T :=
      match DList.get v Delta  with 
        | None =>  (DList.set v (Some w) Delta)
        | Some x => Delta
      end.
    
  End t. 
  
  Definition init (Phi : state ): T Phi := DList.init (fun _ => None) Phi. 
  
  Fixpoint apply (Phi : state) : T Phi -> DList.T eval_sync Phi -> DList.T eval_sync Phi :=
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
        (* | Try a =>  *)
        (*     let a := eval_action _ a in  *)
        (*       Dyn.Try Phi a                     *)
        | OrElse t a b => Dyn.OrElse Phi (eval_action _ a) (eval_action _ b)  
      end.                 
    
  End t. 
  Arguments eval_action {Phi} {t} _%action _ _.  

End Sem.           

Definition Eval Phi (st: eval_state Phi)  t (A : Action Phi t ) Delta :=  @Sem.eval_action Phi t (A _) st Delta. 

Definition Next Phi st (A : Action Phi Tunit) := 
  let Delta := Eval Phi st _ A (Diff.init Phi) in 
    match Delta with 
      | None => st
      | Some Delta => Diff.apply Phi (snd Delta) st
    end. 

