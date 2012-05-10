
Require Import Common. 
Inductive type :=
| Tregfile : forall (size : nat) (base : type0) , type
| Tfifo : nat -> type0 -> type
| Tbase : type0 -> type
| Tinput  : type0 -> type
| Toutput : type0 -> type. 


Fixpoint eval_type (t : type) : Type :=
  match t with
    | Tregfile size bt => Regfile.T size (eval_type0 bt)
    | Tfifo n bt => FIFO.T n (eval_type0 bt)
    | Tbase bt => eval_type0 bt
    | Tinput bt => eval_type0 bt
    | Toutput bt => eval_type0 bt
  end. 

Definition eval_list_type := eval_env eval_type. 


Section expr. 
  Variable Env : list type. 
  
  Inductive expr : type0 -> Type :=
  | Eprim : forall f (args: expr_vector (args (f))), expr ( (res (f)))
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

  (* top level expressions *)
  Inductive expr2 : type -> Type :=
  | Eset : forall t , expr t ->  expr2 (Tbase t)
  | Eset_array : forall size n t,
                   expr (Tint n) -> expr t -> expr2 (Tregfile size t)
  (* operations on fifos *)
  | Epush : forall n t, expr t -> expr2 (Tfifo n t)
  | Epop  : forall n t, expr2 (Tfifo n t) (* forgets the first element *)
  | Epushpop : forall n t, expr t -> expr2 (Tfifo n t)
  | Eclear : forall n t, expr2 (Tfifo n t)
                          
  (* set an output *)
  | Eset_output : forall t,  expr t -> expr2 (Toutput t)
    
  (* do nothing *)
  | Enop : forall t, expr2 t.
  
  
  Variable ENV : eval_list_type Env. 

  Fixpoint  eval_expr t (e : expr t) : option (eval_type0 t) :=
    match e with
      | Eprim f args => 
          let eval_expr_vector :=
              fix eval_expr_vector l (v : expr_vector l) {struct v} :  option (eval_type0_list l) :=
              match v with
                | expr_vector_nil => Some tt
                | expr_vector_cons hd q e vq => 
                    do hd <- eval_expr hd e; 
                    do tl <- eval_expr_vector q vq;
                    Some (hd,tl)
              end
          in 
            do args <-  (eval_expr_vector _ args);
          Some (value (f) args)
      | Eget t v => Some (get Env (Tbase t) v ENV)
      | Efirst n bt fifo => 
          let fifo := (get Env (Tfifo n bt) fifo ENV ) in
            @FIFO.first (eval_type0 bt) n  fifo 
      | Eisfull n bt fifo => 
          let fifo := (get Env (Tfifo n bt) fifo ENV ) in 
            Some (@FIFO.isfull _ n fifo)
      | Eisempty n bt fifo => 
          let fifo := (get  Env (Tfifo n bt) fifo ENV ) in 
            Some  (@FIFO.isempty _ n fifo)
      | Eget_input bt x => 
          let x := get  Env (Tinput bt) x ENV in 
            Some x
      | Eget_output bt x => 
          let x := get  Env (Toutput bt) x ENV in 
            Some x
      | Eget_array size n bt v idx  => 
          let v := get  Env (Tregfile size bt) v ENV in 
            do idx <- eval_expr _ idx;
          @Regfile.get size _ v (Word.unsigned idx)
    end. 

  Fixpoint eval_expr2 t (e : expr2 t) : eval_type t ->  option (eval_type t) :=
    match e with
      | Eset t e => 
          fun r => eval_expr t e
      | Eset_array size n t adr e =>
          fun v => 
            do adr <- eval_expr _ adr;
            do e <- eval_expr _ e;
            let adr := Word.unsigned adr in 
            (* Since Regfile.set silently erases out of bounds
            accesses, we add an extra check here *)
            check (lt_nat_bool adr size);
            Some (@Regfile.set size (eval_type0 t) v adr e) 
      | Epush n t e => 
          fun f =>
            do e <- eval_expr t e;
            Some (FIFO.push e f)               
      | Epop n t => 
          fun f => 
            @FIFO.pop _ n f 
      | Epushpop n t e => 
          fun f => 
            do f <- @FIFO.pop _ n  f; 
            do e <- eval_expr t e;
            Some (FIFO.push  e f)
      | Eclear n t =>
          fun f => Some (FIFO.clear  f)
      | Eset_output t e => 
          fun _ => eval_expr t e
      | Enop t => fun x => Some x
    end. 
End expr. 



(* A transition is parametrized by a memory environment. 
   It contains a guard (a boolean expression), and a dependtly-typed list, which ensure that every memory location is updated.  *)

Record transition Env :=
  { pi : expr Env Tbool;
    alpha : dlist (expr2 Env) Env}.
                    
Definition eval_alpha E (alpha : dlist  (expr2 E) E) :
  eval_list_type E -> option (eval_list_type E) :=
  fun  (X : eval_list_type E) =>
    dlist_fold type (expr2 E) eval_type (eval_expr2 E X) E alpha X.

Record ATS :=
  {
    memory : list type;
    transitions : list (transition (memory))
  }. 

Definition eval_transition (mem: list type) (tr : transition mem) : 
  eval_list_type mem -> option (eval_list_type mem) :=
  fun (E : eval_list_type mem) =>
    let guard := eval_expr mem E Tbool (pi mem tr) in
      match guard with
        | Some true => eval_alpha mem (alpha mem tr) E
        | Some false => None
        | None => None
      end.

Fixpoint eval_transitions mem (l : list (transition mem))  :=
  match l with 
    | nil => fun _ _  => True
    | cons t q => union (fun x y => eval_transition mem t x = Some y) 
                       (eval_transitions mem q)
  end. 
  
Definition eval (X : ATS) :=
  eval_transitions (memory X) (transitions X). 
