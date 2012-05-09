Require Import Common. 

Inductive type : Type :=
| Tlift : type0 -> type
| Ttuple : list type -> type. 

Fixpoint eval_type (t : type) :=
  match t with 
    | Tlift t => eval_type0 t
    | Ttuple l =>
        List.fold_right (fun x acc => eval_type x * acc)%type Datatypes.unit l
  end.    

Inductive sync : Type :=
  | Treg : forall (t : type), sync
  | Tregfile : forall (n : nat) (t : type), sync. 

Definition state := list sync. 
Definition eval_sync (s : sync) := 
  match s with
    | Treg t => eval_type t 
    | Tregfile n t => Regfile.T n (eval_type t)
  end. 

Definition eval_state := eval_env eval_sync. 

Notation Int := (Tlift (Tint 16)).
Notation Bool := (Tlift (Tbool)).
Notation Unit := (Tlift (Tunit)). 

Inductive member {T} : list T -> Type :=
| member_0 : forall l t, member (t::l)
| member_S : forall l t, member l -> member (t :: l). 

Inductive primitive (Phi : state) : list type -> type -> Type:=
  | register_read : forall t, var Phi (Treg t) ->  primitive Phi nil t
  | register_write : forall t, var Phi (Treg t) -> primitive Phi (t:: nil) Unit
  (* register file primitives *)
  | regfile_read : forall n t (v : var Phi (Tregfile n t)) p, primitive Phi ([Tlift (Tint p)])%list  t
  | regfile_write : forall n t (v : var Phi (Tregfile n t)) p, primitive Phi ([Tlift (Tint p); t])%list  Unit. 


Section s.
  
  Variable Phi : state.

  Section t. 
    Variable Var : type -> Type. 
    Inductive expr :  type -> Type :=
    | Evar : forall t (v : Var t), expr t
    | Ebuiltin : forall args res (f : builtin args res), 
                   dlist  (fun j => expr (Tlift j)) (args) -> 
                   expr  (Tlift res)
    | Econstant : forall  (c : constant0), expr (Tlift (cst_ty c))
    | Enth : forall l t (m : var l t), expr (Ttuple l) -> expr t
    | Etuple : forall l (exprs : dlist (expr) l), expr (Ttuple l). 
    
    Inductive action : type -> Type :=
    | Return : forall t (exp : expr t), action t
    | Bind :
      forall t u 
        (a : action  t) 
        (f : Var t -> action u),  
        action u
    | When : forall t (e : expr Bool) (a : action t), action t
    | Primitive : 
      forall args res (p : primitive Phi args res)
        (exprs : dlist (expr) args),
        action res. 
  End t. 
  Definition Action t := forall Var, action Var t.
  Definition Expr t := forall Var, expr Var t. 


  Notation eval_type_list := (List.fold_right (fun x acc => eval_type x * acc)%type Datatypes.unit). 
  
  Definition eval_expr (t : type) (e : expr eval_type t) : eval_type t. 
  refine ( 
      let fix eval_expr t e {struct e}:=
          match e with
            | Evar t v => v
            | Ebuiltin args res f x => 
                let exprs := 
                    _
                in
                  builtin_denotation args res f exprs                            
            | Econstant c => cst_val c
            | Etuple l exprs => 
                dlist_fold' eval_expr l exprs 
            | Enth l t v e => 
                get l t v (eval_expr (Ttuple l) e)
          end 
      in eval_expr t e). 
  
  refine (let fix fold l (dl : dlist (fun j => expr eval_type (Tlift j)) l) : eval_env eval_type0 l :=
              match dl with 
                | dlist_nil => tt
                | dlist_cons _ _ t q => (eval_expr _ t,fold _ q)
              end in fold args x). 

  Defined. 


End s. 


Delimit Scope expr_scope with expr. 
Delimit Scope action_scope with action. 
  

(** * Actions *)
  
Arguments Bind {Phi Var t u} _%action _%action. 
Notation "'DO' X <- A ; B" := (Bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200) : action_scope. 

Arguments When {Phi Var t} _%expr _%action. 
Notation " 'WHEN' e ; B" := (When e B) (at level 200, e at level 100, B at level 200). 

Arguments Return {Phi Var t} _%expr. 
Notation " 'RETURN' e" := (Return e) (at level 200, e at level 100). 

Arguments Primitive {Phi Var} args res _ _%expr. 

(** * Primitives *)
Arguments register_read {Phi t} _. 
Notation "'read' [: v ]" := (Primitive nil _ (register_read v) dlist_nil) (no associativity).

Arguments register_write {Phi t} _. 
Notation "'write' [: v <- w ]" := (Primitive (cons _ nil) Unit (register_write v) (dlist_cons (w)%expr (dlist_nil))) (no associativity). 

Arguments regfile_read {Phi n t} _ p. 
Notation "'read' M [: v ]" := (Primitive ([Tlift (W _)])%list _ (regfile_read M _ ) (dlist_cons (v)%expr (dlist_nil))) (no associativity). 

Arguments regfile_write {Phi n t} _ p. 
Notation "'write' M [: x <- v ]" := (Primitive ([Tlift (W _); _])%list _ (regfile_write M _ ) (dlist_cons (x)%expr (dlist_cons (v)%expr (dlist_nil)))) (no associativity). 

(** * Expressions  *)
Arguments Enth  {Var l t} m _%expr. 
Arguments Evar  {Var t} _. 
Notation "! x" := (Evar x) (at level  10) : expr_scope . 

Arguments Ebuiltin {Var} {args res} _ _%expr. 
Notation "{< f ; x ; y >}" := (Ebuiltin f (dlist_cons  (x)%expr (dlist_cons (y)%expr dlist_nil))).
Notation "{< f ; x >}" := (Ebuiltin f (dlist_cons (x)%expr dlist_nil)).

Notation "~ x" :=  ({< BI_negb ; x >}) : expr_scope. 
Notation "a || b" := ({< BI_orb ; a ; b >}) : expr_scope. 
Notation "a - b" := ({< BI_minus _ ; a ; b >}) : expr_scope. 
Notation "a + b" := ({< BI_plus _ ; a ; b >}) : expr_scope. 
Notation "a = b" := ({< BI_eq _ ; a ; b >}) : expr_scope. 
Notation "a < b" := ({< BI_lt _ ; a ; b >}) : expr_scope. 
Notation "x <= y" := ((x < y) || (x = y))%expr : expr_scope. 
Notation "x <> y" := (~(x = y))%expr : expr_scope. 

Arguments Econstant {Var} _.  
Notation "#i x" := (Econstant (Cword x)) (at level 0). 
Notation "#b x" := (Econstant (Cbool x)) (at level 0). 
Notation "#" := Econstant. 

Definition Ctt : constant0 := mk_constant (Tunit) tt. 

Record TRS : Type := mk_TRS
  {
    Phi : state; 
    rules : list (Action Phi Unit)
  }. 



Definition comp {A B C} (f : B -> C) (g : A -> B) := fun (x : A) => f (g (x)). 
Notation "f ∘ g" := (comp f g) (at level 60). 

Module Diff. 
  Section t. 
    Variable Phi : state. 
    Definition T := eval_env (option ∘ eval_sync) Phi. 
    Definition add (Delta : T) t (v : var Phi t) w : option T :=
      match get Phi t v Delta  with 
        | None =>  Some  (set _ _ Phi t v (Some w) Delta)
        | Some _ => None 
      end.
      
  End t. 
  Fixpoint init (Phi : state ): T Phi := 
    match Phi with 
      | nil => tt
      | cons t Phi => (None, init Phi)
    end. 
   
  Fixpoint apply (Phi : state) : T Phi -> eval_env eval_sync Phi -> eval_env eval_sync Phi :=
    match Phi with 
      | nil => fun _ _ => tt
      | cons t Phi => fun Delta E => 
                     match fst Delta with 
                       | None => (fst E, apply Phi (snd Delta) (snd E))
                       | Some d => (d, apply Phi (snd Delta) (snd E))
                     end
    end. 

End Diff. 


Module Sem. 

  Module Dyn. 
  (** dynamic semantics: 
    - continuation passing style: the current diff is threaded through the execution 
    - illegal behaviors are denoted by None *)
    Section t. 
      Variable Phi : state. 
      
      Definition T t := eval_state Phi -> Diff.T Phi -> option (t * Diff.T Phi). 
      Definition Return {t} (e : t) : T t  := fun st d => Some (e, d).
      Definition Bind {s t} : T s -> (s -> T t) -> T t :=
        fun (x : T s) (f : s -> T t) (st : eval_state Phi) (d : Diff.T Phi) => 
          match x st d with 
              Some (e, d') =>  f e st d' 
            | None => None
          end. 
      Definition Fail {t} : T t := fun _ _ => None. 
      
      Definition Run (CMD : T unit) (st : eval_state Phi) := 
        match CMD st (Diff.init Phi) with 
          | None => None 
          | Some Delta => Some (Diff.apply Phi (snd Delta) st)
        end. 
      Definition primitive_denote  args res (p : primitive Phi args res) (exprs : eval_env eval_type args) : T (eval_type res).  
      destruct p;  simpl in *; intros st Delta. 
      exact (Some (get Phi _ v st, Delta)).
      destruct exprs as [w _]. 
      refine (match Diff.add _ Delta _ v w with | None => None | Some Delta => Some (tt, Delta) end). 
      refine (let rf := get Phi (Tregfile n t) v st in 
              let adr := fst exprs in 
              match @Regfile.get n _ rf  (Word.unsigned adr) with 
                  | None => None
                  | Some v => Some (v, Delta)
              end). 
      refine (
          let rf := get Phi (Tregfile n t) v st in 
          let rf := match exprs with 
            | (adr, (w, _)) => @Regfile.set n _ rf (Word.unsigned adr) w
          end in 
            match Diff.add _ Delta _ v rf with 
                | None => None 
                | Some (Delta) => Some (tt, Delta)
          end). 
                      
      Defined. 
    End t. 
  End Dyn. 

  (** dynamic semantics: 
    - all guard failures are represented by None. 
    - continuation passing style: the current diff is threaded through the execution 
  *)
  Section t. 
    Variable Phi : state. 
    Definition eval_action (t : type) (a : action Phi eval_type t) : 
      (Dyn.T Phi (eval_type t)). 
  refine (
      let fix eval_action (t : type) (a : action Phi eval_type t) :
          Dyn.T Phi ( eval_type t) :=
          match a with
            | Return t exp => Dyn.Return Phi (eval_expr _ exp)
            | Bind t u a f => 
                let act := eval_action _ a in 
                let f' := (fun e => eval_action u (f e)) in 
                  Dyn.Bind Phi act f'              
            | When t e a => 
                let g1 := eval_expr _ e in 
                let a' := eval_action t a in 
                match g1 with 
                  | true => a' 
                  | false => Dyn.Fail  Phi
                end
            | Primitive args res p exprs => 
                Dyn.primitive_denote Phi args res p (dlist_fold' eval_expr _ exprs)
          end                
      in  eval_action t a). 
  Defined.
  End t. 


End Sem.           

Section run. 

  Variable T : TRS. 
  Notation rule := (Action (Phi T) Unit). 

  Definition run_rule (R : rule) := 
    fun st => Sem.Dyn.Run _ (Sem.eval_action _ _ (R eval_type)) st. 
                        
  Fixpoint first_rule (l : list rule) x :=
    match l with 
      | nil => Some x
      | cons R q => 
          match run_rule R x with 
            | None => first_rule q x
            | Some x => Some x 
          end
    end. 
  
  Fixpoint iter_option {A} n (f : A -> option A) x :=
    match n with 
      | 0 => Some x
      | S n => match f x with | None => Some x | Some x => iter_option n f x end 
    end. 

  Fixpoint run_unfair n x :=
    match n with 
      | 0 => Some x
    | S n => 
        match first_rule (rules T) x with 
          | None => Some x
          | Some x => run_unfair n x
        end
  end. 

End run. 

Open Scope action_scope. 

