Require Import Common. 
(* Require Import DList.  *)

Inductive type : Type :=
| Tlift : type0 -> type
| Ttuple : list type -> type. 

Fixpoint eval_type (t : type) :=
  match t with 
    | Tlift t => eval_type0 t
    | Ttuple l => ETuple.of_list eval_type l
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

Definition eval_state := Tuple.of_list eval_sync. 

Notation Int := (Tlift (Tint 16)).
Notation Bool := (Tlift (Tbool)).
Notation Unit := (Tlift (Tunit)). 


Inductive primitive (Phi : state) : list type -> type -> Type:=
  | register_read : forall t, var Phi (Treg t) ->  primitive Phi nil t
  | register_write : forall t, var Phi (Treg t) -> primitive Phi (t:: nil) Unit
  (* register file primitives *)
  | regfile_read : forall n t (v : var Phi (Tregfile n t)), primitive Phi ([Tlift (Tfin n)])%list  t
  | regfile_write : forall n t (v : var Phi (Tregfile n t)), primitive Phi ([Tlift (Tfin n); t])%list  Unit.


Section s.
  
  Variable Phi : state.

  Section t. 
    Variable Var : type -> Type. 
    Inductive expr :  type -> Type :=
    | Evar : forall t (v : Var t), expr t
    | Ebuiltin : forall args res (f : builtin args res), 
                   DList.T  (fun j => expr (Tlift j)) (args) -> 
                   expr  (Tlift res)
    | Econstant : forall  ty (c : constant0 ty), expr (Tlift ty)
                          
    | Emux : forall t, expr Bool -> expr t -> expr t -> expr t 

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
    | Assert : forall (e : expr Bool), action Unit
    | Primitive : 
      forall args res (p : primitive Phi args res)
        (exprs : DList.T (expr) args),
        action res 
    (* | Try : forall (a : action Unit), action Unit *)
    | OrElse : forall t, action t -> action t -> action t.
  End t. 
  Definition Action t := forall Var, action Var t.
  Definition Expr t := forall Var, expr Var t. 

  Notation eval_type_list := (ETuple.of_list eval_type). 
  
  Definition eval_expr (t : type) (e : expr eval_type t) : eval_type t. 
  refine ( 
      let fix eval_expr t e {struct e}:=
          match e with
            | Evar t v => v
            | Ebuiltin args res f exprs => 
                let exprs := 
                    DList.to_tuple  
                      (fun (x : type0) (X : expr eval_type (Tlift x)) =>
                         eval_expr (Tlift x) X)
                      exprs
                in
                  builtin_denotation args res f exprs                            
            | Emux t b x y => if eval_expr _ b then eval_expr t x else eval_expr t y
            | Econstant ty c => c
            | Etuple l exprs => 
                DList.to_etuple eval_expr exprs
            | Enth l t v e => 
                ETuple.get l t v (eval_expr (Ttuple l) e)
            | Efst l t  e => 
                ETuple.fst _ _ (eval_expr _ e)
            | Esnd l t  e => 
                ETuple.snd _ _  (eval_expr _ e)
          end 
      in eval_expr t e). 
  Defined. 


End s. 


(** * Actions *)
Delimit Scope expr_scope with expr. 
Delimit Scope action_scope with action. 
  

Arguments Bind {Phi Var t u} _%action _%action. 
Notation "'DO' X <- A ; B" := (Bind A (fun X => B)) (at level 200, X ident, A at level 100, B at level 200) : action_scope. 

(* Arguments Try {Phi%list Var} _%action.   *)
(* Notation "'TRY' A " := (Try A) (at level 40) : action_scope.  *)

Arguments Assert {Phi Var} e%expr. 

Definition When {Phi Var t} e a : action Phi Var t := @Bind Phi Var _ _ (Assert e) (fun _ => a). 
Arguments When {Phi Var t} _%expr _%action. 
Notation " 'WHEN' e ; B" := (When e B) (at level 200, e at level 100, B at level 200). 

Arguments Return {Phi Var t} _%expr. 
Notation " 'RETURN' e" := (Return e) (at level 200, e at level 100). 

Arguments Primitive {Phi Var} args res _ _%expr. 

(** * Primitives *)
Arguments register_read {Phi t} _. 
Notation "'read' [: v ]" := (Primitive nil _ (register_read v) DList.nil) (no associativity).

Arguments register_write {Phi t} _. 
Notation "'write' [: v <- w ]" := (Primitive (cons _ nil) Unit (register_write v) (DList.cons (w)%expr (DList.nil))) (no associativity). 

Arguments regfile_read {Phi n t} _. 
Notation "'read' M [: v ]" := (Primitive ([Tlift (_)])%list _ (regfile_read M _ ) (DList.cons (v)%expr (DList.nil))) (no associativity). 

Arguments regfile_write {Phi n t} _ . 
Notation "'write' M [: x <- v ]" := (Primitive ([Tlift (_); _])%list _ (regfile_write M _ ) (DList.cons (x)%expr (DList.cons (v)%expr (DList.nil)))) (no associativity). 

(** * Expressions  *)
Arguments Enth  {Var l t} m _%expr. 
Arguments Evar  {Var t} _. 
Notation "! x" := (Evar x) (at level  10) : expr_scope . 

Arguments Ebuiltin {Var} {args res} _ _%expr. 
Notation "{< f ; x ; y ; z >}" := (Ebuiltin f (x :: y :: z :: [])%dlist) : expr_scope. 
Notation "{< f ; x ; y >}" := (Ebuiltin f (x :: y :: [])%dlist) : expr_scope. 
Notation "{< f ; x >}" := (Ebuiltin f (x :: [])%dlist) : expr_scope. 

Notation "~ x" :=  ({< BI_negb ; x >})%expr : expr_scope. 
Notation "a || b" := ({< BI_orb ; a ; b >})%expr : expr_scope. 
Notation "a && b" := ({< BI_andb ; a ; b >})%expr : expr_scope. 
Notation "a - b" := ({< BI_minus _ ; a ; b >})%expr : expr_scope. 
Notation "a + b" := ({< BI_plus _ ; a ; b >})%expr : expr_scope. 
Notation "a = b" := ({< BI_eq _ ; a ; b >})%expr : expr_scope. 
Notation "a < b" := ({< BI_lt _ ; a ; b >})%expr : expr_scope. 
Notation "x <= y" := ((x < y) || (x = y))%expr : expr_scope. 
Notation "x <> y" := (~(x = y))%expr : expr_scope. 

Arguments Econstant {Var ty} _.  
Notation "#i x" := (Econstant (Cword x)) (at level 0). 
Notation "#b x" := (Econstant (Cbool x)) (at level 0). 
Notation "#" := Econstant. 

Definition Ctt : constant0 Tunit := tt. 

Record TRS : Type := mk_TRS
  {
    Phi : state; 
    rules : list (Action Phi Unit)
  }. 

Module Diff. 
  Section t. 
    Variable Phi : state. 
    Definition T := Tuple.of_list (option ∘ eval_sync) Phi. 
    (* first *)
    Definition add (Delta : T) t (v : var Phi t) w :  T :=
      match Tuple.get Phi t v Delta  with 
        | None =>  (Tuple.set _ _ Phi t v (Some w) Delta)
        | Some x => Delta
      end.
    
  End t. 
  Fixpoint init (Phi : state ): T Phi := 
    match Phi with 
      | nil => tt
      | cons t Phi => (None, init Phi)
    end. 
  
  Fixpoint apply (Phi : state) : T Phi -> Tuple.of_list eval_sync Phi -> Tuple.of_list eval_sync Phi :=
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
      
      (* Definition Try : T unit -> T unit :=  *)
      (*   fun a st Delta =>  *)
      (*     match a st Delta with  *)
      (*       | None => Some (tt, Delta) *)
      (*       | x =>  x *)
      (*     end.  *)
                                          
        
      Definition Run (CMD : T unit) (st : eval_state Phi) := 
        match CMD st (Diff.init Phi) with 
          | None => None 
          | Some Delta => Some (Diff.apply Phi (snd Delta) st)
        end. 

      Definition primitive_denote  args res (p : primitive Phi args res) (exprs : Tuple.of_list eval_type args) : T (eval_type res). 
      refine (match
          p in (primitive _ l t) return (Tuple.of_list eval_type l -> T (eval_type t))
        with
          | register_read t v =>
              fun _ (st : eval_state Phi)
                  (Delta : Diff.T Phi) => Some (Tuple.get Phi (Treg t) v st, Delta)
          | register_write t v =>
              fun (exprs : Tuple.of_list eval_type [t]) (_ : eval_state Phi) (Delta : Diff.T Phi) =>
                let (w, _) := exprs in                   
                  Some (tt, Diff.add Phi Delta (Treg t) v w)
          | regfile_read n t v  =>
              fun (exprs : Tuple.of_list eval_type [Tlift (Tfin n)]) 
                  (st : eval_state Phi) (Delta : Diff.T Phi) =>
                let rf := Tuple.get Phi (Tregfile n t) v st in
                let adr := fst exprs in
                let v := Regfile.get rf (adr) in Some (v, Delta)
          | regfile_write n t v =>
              fun (exprs : Tuple.of_list eval_type [Tlift (Tfin n); t]) 
                  (st : eval_state Phi) (Delta : Diff.T Phi) =>
                let rf := Tuple.get Phi (Tregfile n t) v st in
                let rf := match exprs with 
                              (adr, (w, _)) => Regfile.set rf adr w
                          end
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
              | Assert e => 
                  let g := eval_expr _ e in 
                    match g with 
                      | true => Dyn.Return Phi tt
                      | false => Dyn.Retry  Phi
                    end
              | Primitive args res p exprs => 
                  Dyn.primitive_denote Phi args res p (DList.to_tuple eval_expr  exprs)
              (* | Try a =>  *)
              (*     let a := eval_action _ a in  *)
              (*       Dyn.Try Phi a                     *)
              | OrElse t a b => Dyn.OrElse Phi (eval_action _ a) (eval_action _ b)  
          end                 
        in  eval_action t a). 

    Defined.
  End t. 
  Arguments eval_action {Phi} {t} _%action _ _.  
  
  (* Lemma sanity Phi a (st : eval_state Phi) Delta x:  *)
  (*   eval_action  a st Delta = Some (x, Delta) ->  *)
  (*   eval_action (Try a) st Delta = Some (x, Delta). *)
  (* Proof.  *)
  (*   intros. simpl. unfold Dyn.Try. rewrite H.  reflexivity. *)
  (* Qed.  *)

  Definition eval_rule {Phi} (R : Action Phi Unit) := 
    fun st st' => match Sem.Dyn.Run _ (Sem.eval_action (R eval_type)) st  with
                      | None => False
                      | Some st'' => st' = st''
       end. 
                     
                      
  Module FSM. 

    Record T (state : Type):= mk_T
      {
        delta : relation state
      }.

  End FSM.

  Inductive star {A} (R : relation A) : relation A :=
  | star_step : forall x y, R x y -> star R x y
  | star_trans : forall x y z, star R x y -> R y z -> star R x z. 
 
  Definition eval_TRS (T : TRS) : FSM.T (eval_state (Phi T)) :=
    let delta := List.fold_left (fun acc t => union (eval_rule t) acc) (rules T) (fun _ _  => False) in
    FSM.mk_T _ (star delta). 

End Sem.           

Section run. 

  Variable T : TRS. 
  Notation rule := (Action (Phi T) Unit). 

  Definition run_rule (R : rule) := 
    fun st => Sem.Dyn.Run _ (Sem.eval_action (R eval_type)) st. 
                        
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

Module Ops. 
  Notation rule Phi := (Action Phi Unit). 

  (** * A simple round-robin scheduler 

      The simplest scheduler one could imagine _try_ to fire one rule
      each cycle; but the rule may fail. This is a (weakly) fair
      scheduler, that applies rules one by one in a given order, if
      possible, and moving to the next rule if not. 

  *)
  Definition round_robin (Phi : state) (l : list (rule Phi)) : {Phi' : state & rule Phi'}. 
  refine 
    (
      let n := List.length l in 
      let c := Treg (Tlift (Tfin n)) in 
      let Phi' := (Phi ++ [c])%list  in _
    ). 
   exists Phi'. 
   intros Var. 
   Definition lift Var Phi Psi t : action Phi Var t -> action (Phi ++ Psi)%list Var t. Admitted. 
   assert (v : var Phi' c ). clear. admit. 
   (* refine ( *)
   (*    let fold := fix fold v' n l := *)
   (*        match l with  *)
   (*          | nil => Return (#Ctt) *)
   (*          | cons t q =>  *)
   (*              let t := lift _ _ _ _ (t Var) in  *)
   (*              OrElse _ _ _ ( _ ) (fold v' (S n) q) *)
   (*        end *)
   (*    in  *)
   (*      DO v' <- read [: v ];   *)
   (*      DO _ <- fold v' 0 l;  *)
   (*      write [: v <- {< BI_next _ ; !v' >}   ] *)
   (*  )%action.  *)
   (* (* refine (TRY *) *)
   (* (*           ( *) *)
   (* (*             WHEN (!v' = # (Finite.repr n0 : constant0 (Tfin n)));  *) *)
   (* (*             (TRY t0) *) *)
   (* (*        ))%action.  *) *)
   Abort. 
  
End Ops.   