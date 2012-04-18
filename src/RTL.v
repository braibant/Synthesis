Require Import Common. 

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

