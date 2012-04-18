Require Export FunctionalExtensionality. 

Delimit Scope iso_scope with iso. 

Set Implicit Arguments. 

Class T (A B : Type) : Type := mk_T
  {
    iso : A -> B;
    uniso : B -> A
  }.

Arguments mk_T {A B} iso uniso.
Arguments iso {A B} T _.
Arguments uniso {A B} T _.

(** We separate the properties and the definition of the function  *)
Class P {A B: Type} (I : T A B):= mk_P
  {
    iso_uniso : forall x, iso I (uniso I x) = x;
    uniso_iso : forall x, uniso I (iso I x) = x
  }.

Section Group. 
  Variable A B C : Type. 
  
  Definition one : T A A := {| iso := @id A ; uniso := @id A |}. 
  Lemma one_P : P one. Proof. firstorder. Qed.

  Definition inv (I : T A B) : T B A := {| iso := uniso I ; uniso := iso I |}. 
  Lemma inv_P (I : T A B): P I -> P (inv I). Proof. firstorder. Qed. 

  Definition compose (I : T A B) (J : T B C) : T A C :=
    {| 
      iso := fun x => iso J (iso I x);
      uniso := fun x => uniso I (uniso J x)
    |}. 

  Lemma compose_P (I : T A B) (J : T B C): P I ->  P J -> P (compose I J).
  Proof. 
    constructor; intros; simpl. 
    do 2 rewrite iso_uniso. reflexivity. 
    do 2 rewrite uniso_iso. reflexivity. 
  Qed. 

End Group. 

Notation "1" := (one _) : iso_scope. 
Notation "I * J" := (compose I J) : iso_scope. 
Notation "- I" := (inv  I) : iso_scope. 


(* extensionnal equality on isos *)
Record equiv {A B} (I J: T A B) := mk_eq
  { equiv_iso : forall (x : A), @iso A B  I x = @iso A B J x;
    equiv_uniso : forall (x : B), @uniso A B  I x = @uniso A B J x}.

Notation "I == J" := (equiv I J) (at level 50). 

  
Section Group_P. 
  Context {A B} (I : T A B) (PI: P I).

  Lemma one_compose_right : (I * 1 == I)%iso. 
  Proof. 
    split; intros x; reflexivity.  
  Qed. 

  Lemma one_compose_left : (1 * I == I)%iso. 
  Proof. 
    split; intros x; reflexivity.  
  Qed. 
  
  Lemma inv_compose : ((- I) * I == 1  )%iso. 
  Proof.
    split; intros x; simpl; rewrite iso_uniso; reflexivity. 
  Qed.

  Context {C D} (J : T B C) (K : T C D) (PJ: P J) (PK : P K). 
  Lemma compose_assoc : ((I * J) * K == I * (J * K))%iso. 
  Proof. 
    split; intros;simpl;reflexivity.  
  Qed. 
End Group_P.


Section Product. 
  Context {A B A' B' : Type}(I : T A B) (J : T A' B') (PI : P I) (PJ : P J).
  
  Definition prod : T (A * A') (B * B'):=
    {| 
      iso := fun x => (iso I (fst x), iso J (snd x));
      uniso := fun x => (uniso I (fst x), uniso J (snd x))
    |}.
    
  Lemma prod_P : P (prod). 
  Proof. 
    constructor. 
    intros [x y]; simpl; do 2 rewrite iso_uniso; reflexivity.
    intros [x y]; simpl; do 2 rewrite uniso_iso; reflexivity.
  Qed. 
End Product. 

(* One need to unfold these combinators in the proofs *)
Section wrap. 
  Context {A : Type}.
  Definition select_left {n} {m} (x : (n + m) -> A) : n -> A := 
    fun e => (x (inl _ e)).
  Definition select_right {n} {m} (x : (n + m) -> A) : m -> A := 
    fun e => (x (inr _ e)).
  Definition lift {n} {m} (f : m -> n) (x : n -> A) : m -> A :=
    fun e => x (f e).

  Definition app {n m} (x : n -> A) (y : m -> A) : n + m -> A :=
    fun e => match e with inl e => x e | inr e => y e end. 
End wrap. 

(* Concrete isomorphisms *)
Section Concrete.
  Context {X : Type}.
  Program Definition zero : T (False -> X) unit :=
    {|
      iso   := fun _ => tt;
      uniso := fun _ x => match x with end 
    |}.

  Lemma zero_P : P zero. 
  Proof. 
    constructor. 
    intros []; reflexivity. 
    intros; apply functional_extensionality; intros []. 
  Qed.

  
  Program Definition unit : T (unit -> X) X := 
    {|
      iso   := fun f => f tt;
      uniso := fun e x => match x with | tt => e end 
    |}.
  
  Lemma unit_P : P unit. 
  Proof. 
    constructor. 
    intros x; reflexivity. 
    intros; apply functional_extensionality. intros []; reflexivity. 
  Qed.
  
  Section sum. 

  Context {A B sigma tau : Type} (I : T (A -> X) sigma)  (J : T (B -> X) tau) (PI : P I) (PJ : P J). 
  Definition sum : T (A + B -> X) (sigma * tau) := 
      {|
        iso := fun X : A + B -> X => 
          (iso I (select_left X), iso J (select_right X));
        uniso := fun x : sigma * tau =>let (a, b) := x in
          app (uniso I a) (uniso J b)
      |}.

  End sum.   
End Concrete.   



