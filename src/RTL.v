Require Import Common. 

Definition map A B := A -> option B. 

Section expr. 
  Variable mems : list type0. 
  Variable regs : list type0. 

  Inductive expr : type0 -> Type :=
  | get_reg : forall t, var regs t ->  expr t
  | get_mem : forall t, var mems t ->  expr t
  | const : forall (c : constant),  expr (cst_ty c)
  | op :
    forall (f : signature), 
      dlist expr (args f) -> 
      expr (res f). 

  Inductive com : Type :=
    | Cskip 
    | Cseq : com -> com -> com
    | Cset_reg : forall t (v : var regs t), expr t -> com
    | Cset_mem : forall t (v : var mems t), expr t -> com
    | Cifb : expr Tbool -> com  -> com -> com. 
  
    
  Record state :=
    {
      st_mems : eval_env eval_type0 mems;
      st_regs : eval_env eval_type0 regs    
    }. 

  Reserved Notation " c1 '/' st '==>' st'" (at level 40, st at level 39).
  Definition eval_expr {t} : state -> expr t -> eval_type0 t. 
  Admitted. 

  Definition update_reg : forall {t},  state -> var regs t ->  eval_type0 t -> state. Admitted. 
  Definition update_mem : forall {t},  state -> var mems t -> eval_type0 t -> state. Admitted. 
  
  Inductive com_eval : com -> state -> state -> Prop :=
  | Eskip : forall st, Cskip  / st ==> st
  | Eseq : forall st1 st2 st3 c1 c2, 
             c1 / st1 ==> st2 ->
             c2 / st2 ==> st3 -> 
             Cseq c1 c2 / st1 ==> st3
  | Eset_reg : forall t (v : var regs t) (e : expr t) st1 st2 r, 
                 eval_expr  st1 e = r ->
                 update_reg  st1 v r = st2 -> 
                 (Cset_reg t v e) / st1 ==> st2 
  | Eset_mem : forall t (v : var mems t) (e : expr t) st1 st2 r, 
                 eval_expr st1 e = r ->
                 update_mem st1 v r = st2 -> 
                 (Cset_mem t v e) / st1 ==> st2
  | Eifb_true : forall (e : expr Tbool) c1 c2 st1 st2, 
                  eval_expr  st1 e = true -> 
                  c1 / st1 ==> st2 ->
                  (Cifb e c1 c2) / st1 ==> st2
  | Eifb_false : forall (e : expr Tbool) c1 c2 st1 st2, 
                   eval_expr st1 e = false -> 
                   c2 / st1 ==> st2 ->
                   (Cifb e c1 c2) / st1 ==> st2 
   where "c1 '/' st '==>' st'" := (com_eval c1 st st').

Fixpoint com_denote (c : com) (st1 : state) : option state :=
  match c with
    | Cskip => Some st1
    | Cseq c1 c2 => 
        do st2 <- com_denote c1 st1;
        com_denote c2 st2
    | Cset_reg t v e =>
        let r := eval_expr st1 e in 
          Some (update_reg st1 v r)
    | Cset_mem t v e =>
        let r := eval_expr st1 e in 
          Some (update_mem st1 v r)
    | Cifb e c1 c2  =>
        let r := eval_expr st1 e in 
          if r then com_denote c1 st1 
          else  com_denote c2 st1
  end. 
End expr.  

Record RTL :=
  {
    mems : list type0;
    regs : list type0;
    code : com mems regs; 
    t_outputs : list type0;
    outputs : dlist (var regs) t_outputs;
    t_inputs : list type0;
    inputs : dlist  (var regs) t_inputs
  }. 


Section semantics. 
  Variable R : RTL. 
  
  Let I := eval_env eval_type0 (t_inputs R). 
  Let O := eval_env eval_type0 (t_outputs R). 

  Let sigma := state (mems R) (regs R). 

  Definition M : Moore.T I O sigma.
  constructor. 
  Fixpoint zob E F (l : dlist  (var E) F) : 
    eval_env eval_type0 E -> eval_env eval_type0 F :=
  match l with
    | dlist_nil => fun _ => tt
    | dlist_cons t q T Q => fun X => (get E t T X, zob _ _ Q X)
  end. 
  
  intros. eapply zob. apply outputs. apply (st_regs _ _ X). 
  intros. apply com_denote. apply (code  R). 
  apply X. 
  Defined. 

End semantics. 
 (*
Inductive machine :=
  {
    mems : list type0;
    regs : list type0;
    instances : list machine;
    reset : com mems regs ;
    step : com mems regs
  }. 

Inductive state (m : machine) := 
  {
    ls : local_state (mems m) (regs m);
    st_machines : dlist _ state (instances m)
  }.
  
Reserved Notation " c1 '/' st '==>' st'" (at level 40, st at level 39).

Inductive com_eval m : com (mems m) (regs m) -> state m -> state m -> Prop :=
  | Eskip : forall st, Cskip (mems m) (regs m)  / st ==> st
  | Eseq : forall st1 st2 st3 c1 c2, 
             c1 / st1 ==> st2 ->
             c2 / st2 ==> st3 -> 
             Cseq (mems m) (regs m) c1 c2 / st1 ==> st3
  | Eset_reg : forall t (v : var (regs m) t) (e : expr (mems m) (regs m) t) st1 st2 r, 
                 eval_expr _ _ st1 e = r ->
                 update_reg _ _ st1 r = st2 -> 
                 (Cset_reg _ _ _ t v e) / st1 ==> st2 (*
  | Eset_mem : forall t (v : var mems t) (e : expr t) st1 st2 r, 
                 eval_expr _ st1 e = r ->
                 update_mem _ st1 r = st2 -> 
                   (Cset_mem t v e) / st1 ==> st2
    | Eifb_true : forall (e : expr Tbool) c1 c2 st1 st2, 
               eval_expr _ st1 e = true -> 
               c1 / st1 ==> st2 ->
               (Cifb e c1 c2) / st1 ==> st2
    | Eifb_false : forall (e : expr Tbool) c1 c2 st1 st2, 
               eval_expr _ st1 e = false -> 
               c2 / st1 ==> st2 ->
               (Cifb e c1 c2) / st1 ==> st2 *)
    where "c1 '/' st '==>' st'" := (com_eval _ c1 st st').
 





End expr. 
  

End expr. 
Inductive type :=
| Tregfile : forall (size : nat) (base : type0) , type
| Tfifo : nat -> type0 -> type
| Tbase : type0 -> type
| Tinput  : type0 -> type
| Toutput : type0 -> type. 

Fixpoint eval_type (t : type) : Type :=
  match t with
    | Tregfile size bt =>Regfile.T size (eval_type0 bt) 
    | Tfifo n bt => FIFO.T n (eval_type0 bt)
    | Tbase bt => eval_type0 bt
    | Tinput bt => eval_type0 bt
    | Toutput bt => eval_type0 bt
  end. 

Section expr. 
  Variable Env : list type. 
  
  Inductive expr : type0 -> Type :=
  | Eprim : forall f (args: expr_vector (args (f))), expr ( (res ( f)))
  | Eget : forall t (v : var Env (Tbase t)), expr t
  (* operations on arrays *)
  | Eget_array : forall size  n t (v : var Env (Tregfile size t)), expr (Tint n) -> expr t
  (* operations on fifo *)
  | Efirst : forall n t (v : var Env (Tfifo n t)), expr t
  | Eisfull : forall n t (v : var Env (Tfifo n t)), expr (Tbool)
  | Eisempty : forall n t (v : var Env (Tfifo n t)), expr (Tbool)
  (* operations on Inputs *)
  | Eget_input : forall t (v : var Env (Tinput t)), expr t
  (* operations on Outputs *)
  | Eget_output : forall t (v : var Env (Toutput t)), expr t
                                                      with expr_vector : list type0 -> Type :=
  | expr_vector_nil : expr_vector nil
  | expr_vector_cons : forall t q, expr  (t) -> expr_vector q -> expr_vector (t::q). 


  Record reg_update (t : type0): Type :=
    {
      latch_enable : expr Tbool;
      data : expr t
    }. 
  
  Record array_update (size : nat) (width : nat) (t : type0) :=
    {
      write_addr : expr (Tint width);
      write_data : expr t;
      write_enable : expr Tbool
    }.

  Record fifo_update (t : type0) :=
    {
      enqueue_data : expr t;
      enqueue_enable : expr Tbool;
      dequeue_enable : expr Tbool;
      clear_enable : expr Tbool
    }. 
  
  Inductive expr2 : type -> Type :=
  (* expression to affect and latch enable  *)
  | Eregister : forall t, reg_update t -> expr2 (Tbase t)
  (* array operations *)
  | Earray :  forall size width t, array_update size width t -> 
                   expr2 (Tregfile size t)
  (* fifo operations *)
  | Efifo : forall n t, fifo_update t ->  expr2 (Tfifo n t) 
  | Enop : forall t, expr2 t. 
              
  
End expr. 

*)