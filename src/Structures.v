
(** Total order relation  *)
Class order (A : Type) := 
  mk_order
    {
      le : A -> A -> bool;
      le_transitive : forall x y z, le x y = true -> le y z = true -> le x z = true;
      le_total  : forall x y , le x y = true \/ le y x = true;
      le_antisym : forall x y, le x y = true -> le y x = true -> x = y
    }.

Notation "x <= y" := (le x y).
Notation "x < y" := (negb (le y x)).

Section ops. 
  Context {A : Type} {O : order A}.
  
  (* min, max operations *)
  Definition min x y := if x <= y then x else y. 
  Definition max x y := if x <= y then y else x. 

  (* compare and swap operation *)
  Definition cmp (x y: A) := (min x y, max x y).
  
  Lemma le_reflexive : forall x, x <= x = true. 
  Proof. 
    intros; destruct (le_total x x); auto. 
  Qed. 
End ops. 


Section monotony.

  (** Monotone functions preserve le *)

  Context {A B : Type} (PA : order A) (PB : order B) (f : A -> B).
  
  Record monotone :=
    {
      proper_eq : forall a b, a = b -> f a = f b;
      proper_le :> forall a b, le a b = true -> le (f a) (f b) = true
    }.
  

  (** min and max commute with monotone functions *)

  Hypothesis Hf : monotone.

  Lemma min_commute : forall (x y: A), f (min x y) = min (f x) (f y). 
  Proof. 
    intros. 
    unfold min. 
    destruct (x <= y) eqn:Hxy; destruct (f x <= f y) eqn:Hfxy; trivial. 
    apply Hf in Hxy. congruence. 
    destruct (le_total x y). congruence. apply Hf in H. eauto using le_antisym. 
  Qed. 
  
  Lemma max_commute : forall (x y: A), f (max x y) = max (f x) (f y). 
  Proof. 
    intros. 
    unfold max. 
    destruct (x <= y) eqn:Hxy; destruct (f x <= f y) eqn:Hfxy; trivial. 
    apply Hf in Hxy. congruence. 
    destruct (le_total x y). congruence. apply Hf in H. eauto using le_antisym. 
  Qed. 

End monotony. 

(** The natural order structures on Booleans *)
Instance bool_order : order bool. 
Proof. 
  refine (mk_order bool (fun x y => negb x || y)%bool _ _ _).
  intros [|] [|] [|]; try discriminate; reflexivity. 
  intros [|] [|]; try discriminate; auto. 
  intros [|] [|]; try discriminate; reflexivity. 
Defined. 
