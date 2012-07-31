Require Import Common. 
Require Word Array. 

(* Require Import DList.  *)
Unset Elimination Schemes. 
Inductive type : Type :=
| Tunit : type 
| Tbool: type 
| Tint: forall (n : nat), type
| Tfin: forall n : nat,  type
(* | Tabstract : ident -> Abstract.T -> type *)
| Ttuple : forall l : list type,  type. 

Section type_ind. 
  Variable P : type -> Prop. 
  Variable Hunit : P Tunit. 
  Variable Hbool : P Tbool. 
  Variable Hint  : forall n, P (Tint n).
  Variable Hfin  : forall n, P (Tfin n). 
  Variable Hnil  : P (Ttuple []). 
  Variable Hcons  : forall t q, P t -> P (Ttuple q) -> P (Ttuple (t :: q)). 

  Definition type_ind (t : type) : P t. 
  refine (let ind := fix ind t : P t :=
              match t with
                | Tunit => Hunit
                | Tbool => Hbool
                | Tint n => Hint n
                | Tfin n => Hfin n
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
    | Tfin n => Finite.T n
    (* | Tabstract _ t => Abstract.carrier t *)
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
                | Tfin n, Tfin m => Nat.eqb n m 
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
      | Tint n => @Word.eq n
      | Tfin n => fun _ _ => false
      | Tbool  => eqb_bool 
      (* | Tabstract _ t => Abstract.eqb t *)
      | Ttuple l => fun _ _ => false
    end. 
  
  Lemma type_eq_correct t x y : type_eq t x y = true -> x = y.
  Proof. destruct t; simpl in *.
    destruct x; destruct y; auto. 
    destruct x; destruct y; auto. 
    intros. apply Word.eq_correct; auto.  
    discriminate. 
    discriminate. 
  Qed. 

  Definition ltb_bool a b :=
    match a, b with
      | false, true => true
      | _, _ => false
    end. 
  
  Fixpoint type_lt (bt : type) : eval_type bt -> eval_type bt -> bool :=
    match bt with
      | Tunit => fun _ _  => true
                              
      | Tbool => ltb_bool 
      | Tint n => @Word.lt n
      | Tfin n => @Finite.ltb n
      (* | Tabstract _ t => Abstract.lt t *)
      | Ttuple _ => fun _ _ => false
    end. 
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

Notation B := Tbool. 
Notation W n := (Tint n).

Inductive builtin : list type -> type -> Type :=
(* | BI_external :  forall (s : signature), builtin (Generics.args s) (Generics.res s) *)
| BI_andb : builtin (B :: B :: nil)%list  B
| BI_orb  : builtin (B :: B :: nil)%list  B
| BI_xorb : builtin (B :: B :: nil)%list  B
| BI_negb : builtin (B  :: nil)%list  B
                    
(* "type-classes" *)
| BI_eq   : forall t, builtin (t :: t :: nil)%list B
| BI_lt   : forall t, builtin (t :: t :: nil)%list B
| BI_mux : forall t, builtin (B :: t :: t :: nil)%list t                         

(* integer operations *)
| BI_plus  : forall n, builtin (W n :: W n :: nil)%list (W n)
| BI_minus : forall n, builtin (W n :: W n :: nil)%list (W n)

| BI_next : forall n, builtin (Tfin (S n) :: nil) (Tfin (S n)). 

Module Builtin. 
  Inductive t : Type :=
  |andb | orb | xorb | negb | eq | lt | mux | plus | minus | next. 
  
  Scheme Equality for t. 

  Definition forget {l r} (b: builtin l r) : t :=
    match b with
        | BI_andb => andb
      | BI_orb => orb
      | BI_xorb => xorb
      | BI_negb => negb
      | BI_eq t => eq
      | BI_lt t => lt 
      | BI_mux t => mux 
      | BI_plus n => plus
      | BI_minus n => minus
      | BI_next n => next
    end. 
End Builtin. 

Definition builtin_eqb {arg res arg' res'} (b : builtin arg res) (b': builtin arg' res') :=
  match b,b' with
    | BI_andb, BI_andb => true
    | BI_orb, BI_orb => true
    | BI_xorb, BI_xorb => true
    | BI_negb, BI_negb => true
    | BI_eq t, BI_eq t' => type_eqb t t' 
    | BI_lt t, BI_lt t' => type_eqb t t'
    | BI_mux t, BI_mux t' => type_eqb t t'
    | BI_plus n, BI_plus m =>  Nat.eqb n m
    | BI_minus n, BI_minus m => Nat.eqb n m
    | BI_next n, BI_next m => Nat.eqb n m
    | _ , _ => false
  end. 

Lemma builtin_eqb_correct l t (b : builtin l t) (b' : builtin l t) :
  builtin_eqb b b' = true -> b = b'. 
Proof.
  intros H. assert (Builtin.forget b = Builtin.forget b'). 
  revert H. destruct b; simpl; try discriminate; destruct b'; simpl; try discriminate; try reflexivity.  
  clear H.
  Import Equality.
  destruct b;
  dependent destruction b'; simpl in *; try discriminate || reflexivity.  
Qed. 


(* applies a ternary function to three arguments *)
Definition tri_op {a b c d } (f : eval_type a -> eval_type b -> eval_type c -> eval_type d) 
  : eval_type_list (a :: b :: c :: nil)%list -> eval_type d :=
  fun X => match X with (x,(y,(z, tt))) => f x y z end. 

(* applies a binary function to two arguments *)
Definition bin_op {a b c} (f : eval_type a -> eval_type b -> eval_type c) 
  : eval_type_list (a :: b :: nil)%list -> eval_type c :=
  fun X => match X with (x,(y,tt)) => f x y end. 

(* applies a unary function to one arguments *)
Definition un_op {a b} (f : eval_type a -> eval_type b) 
  : eval_type_list (a :: nil) -> eval_type b :=
  fun X => match X with (x,tt) => f x end. 

  (* denotation of the builtin functions *)
Definition builtin_denotation (dom : list type) ran (f : builtin dom ran) : 
  eval_type_list dom -> eval_type ran :=
  match f with
    (* | BI_external s => Generics.value s *)
    | BI_andb => @bin_op B B B andb
    | BI_orb =>  @bin_op B B B orb
    | BI_xorb => @bin_op B B B xorb
    | BI_negb =>  @un_op B B negb
    | BI_eq t => @bin_op t t B (type_eq t)
    | BI_lt t => @bin_op t t B (type_lt t)
    | BI_mux t => @tri_op B t t t (fun b x y => if b then x else y) 
    | BI_plus n => @bin_op (W n) (W n) (W n) (@Word.add n)
    | BI_minus n => @bin_op (W n) (W n) (W n) (@Word.minus n)
    | BI_next n => @un_op (Tfin (S n)) (Tfin (S n)) (@Finite.next n)
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

Definition eval_state := DList.T eval_sync. 

(* Notation updates := (Common.Tuple.of_list (Common.comp option  Core.eval_sync) _).  *)
