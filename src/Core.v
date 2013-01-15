Require Import Common. 
Require Import DList. 
Require Word Vector. 


Unset Elimination Schemes. 

(** This file describes the underlying "memory model" of our compiler *)

Inductive type : Type :=
| Tunit : type 
| Tbool: type 
| Tint: forall (n : nat), type
| Ttuple : forall l : list type,  type. 

(** Notations used in the paper  *)
Notation Unit := Tunit.         
Notation B  := Tbool. 
Notation Int n := (Tint n).
Notation Tuple l := (Ttuple l). 

Section type_ind. 
  Variable P : type -> Prop. 
  Variable Hunit : P Tunit. 
  Variable Hbool : P Tbool. 
  Variable Hint  : forall n, P (Tint n).
  Variable Hnil  : P (Ttuple []). 
  Variable Hcons  : forall t q, P t -> P (Ttuple q) -> P (Ttuple (t :: q)). 

  Definition type_ind (t : type) : P t. 
  refine (let ind := fix ind t : P t :=
              match t with
                | Tunit => Hunit
                | Tbool => Hbool
                | Tint n => Hint n
                | Ttuple l => 
                    let fix fold l : P (Ttuple l) :=
                        match l with 
                          | nil => Hnil
                          | cons t q => Hcons t q (ind t) (fold q)
                        end in 
                      fold l
              end 
          in ind t). 
  Defined. 
End type_ind. 
Set Elimination Schemes. 

Fixpoint eval_type st : Type := 
  match st with 
    | Tunit => unit
    | Tbool => bool
    | Tint n => Word.T n
    | Ttuple l => Tuple.of_list eval_type l
  end.    

Definition eval_type_list l : Type := Tuple.of_list eval_type l. 

Require Import NPeano. 

Definition type_eqb : forall a b : type, bool.  
refine (let fix fold a b {struct a}: bool :=
            let fix pointwise   (i j : list type) : bool :=
                match i, j with 
                  | [] , [] => true
                  | t::q , t' :: q' => (fold t t' && pointwise q q')%bool
                  | _, _ => false
                end%list in 
              match a,b with
                | Tunit, Tunit => true
                | Tbool, Tbool => true
                | Tint n,  Tint m => Nat.eqb n m 
                | Ttuple x, Ttuple y => pointwise x y
                | _ , _ => false
              end in fold      
       ). 
Defined. 


Fixpoint type_list_eqb (la lb : list type) : bool :=
  match la,lb with 
    | [], [] => true
    | t :: q , t' :: q' => (type_eqb t t' && type_list_eqb q q' )%bool
    | _ , _ => false
  end%list. 


Lemma nat_eqb_eq : forall x y, Nat.eqb x y = true -> x = y. 
Proof. 
  induction x; destruct y; try reflexivity || simpl; try congruence.
  auto. 
Defined. 

Lemma type_eqb_correct a b : type_eqb a b = true -> a = b. 
Proof. 
  revert b. 
  induction a; induction b; try simpl; try (reflexivity || congruence). 
  intros. apply nat_eqb_eq in H. subst. reflexivity. 
  case_eq (type_eqb a b); simpl; intros. 
  apply IHa in H. subst. repeat f_equal. specialize (IHa0 (Ttuple q0) H0). congruence. 
  discriminate. 
Defined. 

Lemma type_list_eqb_correct la lb : type_list_eqb la lb = true -> la = lb. 
Proof. 
    revert lb; induction la; destruct lb; simpl; try discriminate; intuition.
     rewrite Bool.andb_true_iff in H. destruct H. rewrite (IHla lb); auto. 
     rewrite (type_eqb_correct a t H). reflexivity. 
Qed. 

Lemma type_eqb_refl : forall t, type_eqb t t = true.
Proof.  
  induction t using type_ind; simpl;  firstorder. 
  apply NPeano.Nat.eqb_eq. reflexivity. 
Qed. 
 
(** Operations on types *)
Section type_ops. 
  
  Definition eqb_bool (b1 b2: bool)  :=
    match b1,b2 with 
      | true, true => true
      | false, false => true
      | _,_ => false
    end. 
  
  Fixpoint type_eq (t : type) : eval_type t -> eval_type t -> bool :=
    match t with 
      | Tunit => fun _ _  => true
      | Tint n => @Word.eqb n
      | Tbool  => eqb_bool 
      | Ttuple l => fun _ _ => false
    end. 
  
  Lemma type_eq_correct t x y : type_eq t x y = true -> x = y.
  Proof. destruct t; simpl in *.
    destruct x; destruct y; auto. 
    destruct x; destruct y; auto. 
    intros. apply Word.eqb_correct; auto.  
    discriminate. 
  Qed. 
End type_ops. 


Module Generics.  
  Record signature T (E : T -> Type) := mk_signature
                                         {
                                           args : list T;
                                           res : T; 
                                           value :> Tuple.of_list E args -> E res
  }. 
  
  Arguments mk_signature {T E} args res value. 
  Arguments args {T E} s. 
  Arguments res {T E} s. 
  Arguments value {T E} s _. 
  
  (* could it be a primitive with an empty set of arguments ? *)
  Definition constant T (E : T -> Type) (ty : T) := E ty. 
  Arguments constant {T E} ty. 
End Generics. 

Notation signature := (Generics.signature type eval_type). 
Notation constant := (@Generics.constant type eval_type). 

Definition Cbool b : constant Tbool := b. 
Definition Cword {n} x : constant (Tint n) := (Word.repr _ x). 

(** The definition of state elements. *)
Inductive mem : Type :=
  | Tinput: forall (t: type), mem
  | Treg : forall (t : type), mem
  | Tregfile : forall (n : nat) (t : type), mem. 

Notation Input := Tinput.
Notation Reg   := Treg.
Notation Regfile   := Tregfile.


Definition state := list mem. 

Definition eval_mem (s : mem) := 
  match s with
    | Tinput t => eval_type t
    | Treg t => eval_type t 
    | Tregfile n t => Regfile.T n (eval_type t) 
  end. 

Notation eval_state := (DList.T eval_mem). 
