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
  | Treg : forall (t : type), sync. 

Definition state := list sync. 
Definition eval_sync (s : sync) := match s with Treg t => eval_type t end. 
Definition eval_state := eval_env eval_sync. 

Notation Int := (Tlift (Tint 16)).
Notation Bool := (Tlift (Tbool)).
Notation Unit := (Tlift (Tunit)). 

Inductive member {T} : list T -> Type :=
| member_0 : forall l t, member (t::l)
| member_S : forall l t, member l -> member (t :: l). 

Inductive primitive (Phi : state) : list type -> type -> Type:=
  | register_read : forall t, var Phi (Treg t) ->  primitive Phi nil t
  | register_write : forall t, var Phi (Treg t) -> primitive Phi (t:: nil) Unit. 

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
  Defined. 
  End t. 
End Dyn.           


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
          end 
      in eval_expr t e). 

  refine (let fix fold l (dl : dlist (fun j => expr eval_type (Tlift j)) l) : eval_env eval_type0 l :=
      match dl with 
          | dlist_nil => tt
          | dlist_cons _ _ t q => (eval_expr _ t,fold _ q)
      end in fold args x). 
  Defined. 
  
  (** dynamic semantics: 
    - all guard failures are represented by None. 
    - continuation passing style: the current diff is threaded through the execution 
  *)

  Definition eval_action (t : type) (a : action eval_type t) : 
    (Dyn.T Phi (eval_type t)). 
  refine (
      let fix eval_action (t : type) (a : action eval_type t) :
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
  Definition Action t := forall Var, action Var t.
  Definition Expr t := forall Var, expr Var t. 

End s. 


Notation "'DO' X <- A ; B" := (Bind _ _ _ _ A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200). 

Notation " 'WHEN' e ; B" := (When _ _ _ e B) (at level 200, e at level 100, B at level 200). 
Notation " 'RETURN' e" := (Return _ _ _ e) (at level 200, e at level 100). 
Notation "'read' [: v ]" := (Primitive _ _ nil _ (register_read _ _ v) dlist_nil) (no associativity). 
Notation "'write' [: v <- w ]" := (Primitive _ _ (cons _ nil) Unit (register_write _ _ v) (dlist_cons w (dlist_nil))) (no associativity). 


Notation "{< f ; x ; y >}" := (Ebuiltin _ _ _ (f) (dlist_cons  x (dlist_cons y dlist_nil))).
Notation "{< f ; x >}" := (Ebuiltin _ _ _ (f) (dlist_cons x dlist_nil)).

Delimit Scope expr_scope with expr. 

Notation "~ x" :=  ({< BI_negb ; x >}) : expr_scope. 
Notation "a || b" := ({< BI_orb ; a ; b >}) : expr_scope. 
Notation "a - b" := ({< BI_minus _ ; a ; b >}) : expr_scope. 
Notation "a + b" := ({< BI_plus _ ; a ; b >}) : expr_scope. 
Notation "a = b" := ({< BI_eq _ ; a ; b >}) : expr_scope. 
Notation "a < b" := ({< BI_lt _ ; a ; b >}) : expr_scope. 
Notation "x <= y" := ((x < y) || (x = y))%expr : expr_scope. 
Notation "x <> y" := (~(x = y))%expr : expr_scope. 
Notation "! x" := (Evar _ _ x) (at level  10) : expr_scope . 
Notation "#b x" := (Econstant _ (Cbool x)) (at level 0). 
Notation "#" := Econstant. 
Arguments Econstant {Var} _.  
Definition Ctt : constant0 := mk_constant (Tunit) tt. 

Arguments Econstant {Var} (c). 

Record TRS : Type := mk_TRS
  {
    Phi : state; 
    rules : list (Action Phi Unit)
  }. 


Module GCD. 
  Section t. 
    Variable n : nat. 
    Notation NUM := (Tlift (Tint n)). 
    Notation VAL := (Tlift (Tbool)) (only parsing). 
    Definition Phi : state := Treg VAL :: Treg NUM  :: Treg NUM :: nil. 
  
    Definition iterate : Action Phi Unit. intros V.
    set (c := var_0 : var Phi (Treg VAL)). 
    set (r1 := var_S (var_0) : var Phi (Treg NUM)).  
    set (r2 := var_S (var_S (var_0)) : var Phi (Treg NUM)). 
    refine (DO X <- read [: c]; 
            WHEN (Evar _ _ X); 
            DO A <- read [: r1]; 
            DO B <- read [: r2];
            WHEN (!B <= !A); 
            DO _ <- (write [: r1 <- (!A - !B)%expr]);  
            DO _ <- (write [: r2 <- (!B)%expr]);  
            RETURN #Ctt
           )%expr. 
    Defined. 
    
    Definition done : Action Phi Unit. intros V. 
    set (c := var_0 : var Phi (Treg VAL)). 
    set (r1 := var_S (var_0) : var Phi (Treg NUM)).  
    set (r2 := var_S (var_S (var_0)) : var Phi (Treg NUM)). 
    refine (DO X <- read [: c]; 
            WHEN (!X); 
            DO A <- read [: r1]; 
            DO B <- read [: r2];
            WHEN (!A < !B); 
            DO _ <- (write [: c <- #b false]);  
            DO _ <- (write [: r1 <- !A ]);  
            RETURN #Ctt
           )%expr. 
    Defined. 
    
    Definition T : TRS := mk_TRS Phi (iterate :: done :: nil). 

    Inductive Ty : Type :=
    | RET : Word.T n -> Ty
    | ST : Word.T n -> Word.T n -> Ty. 

    Definition start (x : Ty) : eval_state Phi :=
      match x with 
        | RET a => (false, (a, (a, tt)))
        | ST a b => (true, (a, (b, tt)))
      end.

    Definition finish (x : eval_state Phi) : Ty :=
      match x with 
          | (c,(a,(b,_))) => 
              match c with 
                | true => ST a b
                | false => RET a
              end
      end. 
  End t. 
End GCD. 
  
  


Section run. 

  Variable T : TRS. 
  Notation rule := (Action (Phi T) Unit). 

  Definition run_rule (R : rule) := 
    fun st => Dyn.Run _ (eval_action _ _ (R eval_type)) st. 
                        
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

Definition st0 n x y := GCD.start n (GCD.ST n (Word.repr n x) (Word.repr n y)). 
Definition finish' n x := match x with None => None | Some x => Some (GCD.finish n x) end. 
Eval compute in finish' 16 (run_unfair (GCD.T 16) 5 (st0 16 17 3)). 

