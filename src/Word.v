Require Export ZArith. 
Require Import Eqdep_dec. 
Require Import FunctionalExtensionality. 

Notation "[2^ n ]" := (two_power_nat n). 

(** Implementation of parametric size machine words.  *)

Record T n := mk { val :> Z ; 
                   range : (0 <= val < two_power_nat n)%Z}.
 
Arguments val {n} _. 
Arguments range {n} _. 

Definition unsigned {n} (x : T n) : Z := (val x).

Lemma proof_irrelevance_Zlt n m : forall (p q : Z.lt n m), p = q.
Proof. 
  unfold Z.lt. intros. 
  apply UIP_dec.   
  decide equality. 
Qed. 

Lemma proof_irrelevance_Zle n m : forall (p q : Z.le n m), p = q.
Proof.
  unfold Z.le. intros. apply functional_extensionality_dep; intro x; contradict x; trivial.
Qed.

Lemma unsigned_inj n (u v : T n) :  unsigned u = unsigned v -> u = v.
Proof.
  intros.  unfold unsigned in H.  
  destruct u as [u Hu]; destruct v as [v Hv]. 
  simpl in *. destruct H.
  destruct Hu as [Hu1 Hu2]. 
  destruct Hv as [Hv1 Hv2].
  
  assert (Hu1 = Hv1). apply proof_irrelevance_Zle. subst. 
  assert (Hu2 = Hv2). apply proof_irrelevance_Zlt. subst. 
  reflexivity.
Qed.

Open Scope Z_scope. 

Definition eqb {n} : T n -> T n -> bool := 
  fun x y => 
    (match val x ?= val y with Eq => true | _ => false end) .

Lemma eqb_correct {n} : forall x y : T n, eqb x y = true <-> x = y. 
Proof. 
  split. 
  destruct x; destruct y. unfold eqb; simpl.  
  case_eq (val0 ?= val1); intros; simpl. 
  apply Zcompare_Eq_eq in H. subst.  
  apply unsigned_inj. simpl; auto. 
  discriminate. 
  discriminate. 
  intros. subst. unfold eqb. rewrite Z.compare_refl. reflexivity. 
Defined.


Definition zlt x y := match x ?= y with Lt => true | _ => false end. 
Definition zle x y := match x ?= y with Lt => true | Eq => true | _ => false end. 

Lemma zlt_lt x y: Bool.reflect (x < y) (zlt x y).
Proof. 
  unfold zlt. 
  assert( H:= Zcompare_spec x y).
  revert H. 
  case_eq (x ?= y); intros H Hs; constructor; inversion_clear Hs.
  subst.  apply Zlt_irrefl. 
  auto.
  auto with zarith.
Qed.

Definition signed {n} (x : T n) : Z :=
  if zlt (unsigned  x) [2^ (n - 1)]
  then unsigned  x
  else unsigned  x - [2^n ].


Lemma mod_in_range n:
  forall x, 0 <= Zmod x [2^ n] < [2^ n] .
Proof.
  intro.
  apply (Z_mod_lt x).
  reflexivity. 
Qed.

Definition repr n (x: Z)  : T n := 
  mk n (Zmod x [2^ n]) (mod_in_range n x ).

Definition add {n} : T n -> T n -> T n := fun x y => repr n (x + y ). 
Definition sub {n} : T n -> T n -> T n := fun x y => repr n (x - y). 
Definition mul {n} : T n -> T n -> T n := fun x y => repr n (x * y).  

Definition lt {n} : T n -> T n -> bool := zlt. 
Definition le {n} : T n -> T n -> bool := zle. 

Definition high n m (x : T (n+m)) : T m :=
  repr m (unsigned x / [2^n]).

Definition low n m (x : T (n+m)) : T n :=
  repr n (unsigned x mod [2^n]).

Definition combineLH n m (low : T n) (high : T m)  : T (n+m) :=
  repr (n + m) ((unsigned high)*[2^n] + unsigned low).

Definition andb : T 1 -> T 1 -> T 1 := mul. 
Definition orb  : T 1 -> T 1 -> T 1 := fun x y => repr 1 (Z.max x y). 
Definition negb : T 1 -> T 1 := fun x => repr 1 (1 - x). 
Definition xorb  : T 1 -> T 1 -> T 1 := fun x y => repr 1 (x + y). 

Definition of_bool (b: bool) : T 1 := if b then repr 1 1 else repr 1 0.

Definition zero {n} : T n := repr n 0. 
Definition one {n} : T n := repr n 1. 

Definition opp {n} : T n -> T n := fun x => repr n (-x)%Z. 

Notation "x + y" :=  (add x y). 
Notation "x * y" :=  (mul x y). 
Notation "x - y" :=  (sub x y). 
Notation "0" := zero. 
Notation "1" := one.  

Require Ring_theory. 
  
Section ring. 
  Variable n: nat. 
  Implicit Type  x y z: T n. 

  Lemma add_0_l x : 0 + x = x. 
  Proof.
    apply unsigned_inj. simpl. rewrite Zmod_small.  reflexivity. apply range.       
  Qed. 

  Lemma add_sym x y : x + y = y + x. 
  Proof. 
    apply unsigned_inj. simpl.
    rewrite Z.add_comm.
    reflexivity. 
  Qed. 
    
  Lemma add_assoc x y z : x + (y + z) = (x + y) + z. 
  Proof.
    apply unsigned_inj; simpl. 
    rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. rewrite Z.add_assoc.  reflexivity. 
  Qed. 
    
  Lemma mul_1_l x : one * x = x. 
  Proof.
    apply unsigned_inj; simpl.
    destruct n.  simpl. 
    
    rewrite (Zmod_small 0). 
    Lemma two_power_nat_0 : [2^0] = 1%Z. reflexivity. Qed. 
    Lemma of_size_0 (X: T 0) : unsigned X = 0%Z.  
    Proof. 
      destruct X as [val H]. 
      simpl. rewrite two_power_nat_0 in H. zify; omega.  
      Qed. 
    rewrite of_size_0.  reflexivity. 
    Lemma is_small_0 : 0 <= 0 < [2^0]. rewrite two_power_nat_0.  zify;omega. Qed. 
    Hint Resolve is_small_0 two_power_nat_0. auto.
    rewrite (Zmod_small 1). 
    rewrite Z.mul_1_l. rewrite Zmod_small by apply range. reflexivity.
    clear. 
    Lemma is_small_1 {m}: 0 <= 1 < [2^ S m]. 
    Proof. 
      rewrite two_power_nat_S. replace (2 * [2^m])%Z with ([2^m] + [2^m])%Z by ring.
      split; zify. omega. 
      assert (1 <= [2^m]).
      clear; induction m; zify. rewrite two_power_nat_0. omega. rewrite two_power_nat_S. omega. omega. 
    Qed. 
    Hint Resolve is_small_1. 
    auto. 
  Qed. 
  
  Lemma mul_sym x y : x * y = y * x. 
  Proof. 
    apply unsigned_inj; simpl.
    rewrite Z.mul_comm. 
    reflexivity. 
  Qed. 
  
  Lemma mul_assoc x y z : x * ( y * z ) = (x * y) * z. 
  Proof. 
    apply unsigned_inj; simpl.
    rewrite Zmult_mod_idemp_l,   Zmult_mod_idemp_r. rewrite Z.mul_assoc.  reflexivity. 
  Qed. 
    
  Lemma distr_l x y z: (x + y) * z = (x * z) + (y * z). 
  Proof. 
    apply unsigned_inj; simpl.
    rewrite Zmult_mod_idemp_l. 
    rewrite Z.mul_add_distr_r. 
    rewrite Zplus_mod_idemp_l, Zplus_mod_idemp_r. reflexivity.        
  Qed. 
  
  Lemma sub_def x y : x - y = x + opp y. 
  Proof. 
    apply unsigned_inj; simpl.
    rewrite <- Z.add_opp_r. 
    rewrite Zplus_mod_idemp_r. reflexivity. 
  Qed. 
  
  Lemma opp_def x : x + opp x = zero. 
  Proof. 
    apply unsigned_inj; simpl.
    rewrite Zplus_mod_idemp_r. 
    rewrite Z.add_opp_diag_r. 
    reflexivity. 
  Qed. 
  
End ring. 
Lemma ring n : @Ring_theory.ring_theory (T n) zero one add mul sub opp eq. 
  apply (mk_rt zero one add mul sub opp eq 
               (add_0_l n) (add_sym n) (add_assoc n)
               (mul_1_l n) (mul_sym n) (mul_assoc n) (distr_l n)
               (sub_def n) (opp_def n)
        ) . 
Qed. 

(** Unfortunately it is not possible to define parametrized instances
of the ring of Words. Therefore, one has to declare it each time it is
need. Furthermore, since Add Ring is a vernacular, one cannot add a
new ring based on the context of a proof...  *)

Section test. 
  Variable n : nat. 
  Add Ring word_ring : (ring n). 
  
  Goal forall (x y z: T n), x + y + 1 - y - 1 = x. 
  intros; ring. 
  Qed.
End test. 

Require Import Setoid. 
      (* le_transitive : *)
      (* le_total  : forall x y , le x y = true \/ le y x = true; *)
      (* le_antisym : forall x y, le x y = true -> le y x = true -> x = y *)

Lemma zify_le n : forall (x y : T n), le x y = true <-> (val x <= val y).
Proof. 
  intros. unfold le, zle. rewrite <- Z.compare_le_iff. destruct (x?=y); simpl; intuition congruence. 
Qed. 

Lemma zify_lt n : forall (x y : T n), lt x y = true <-> (val x < val y).
Proof. 
  intros. unfold lt, zlt. rewrite <- Z.compare_lt_iff. destruct (x?=y); simpl; intuition congruence. 
Qed. 

Lemma zify_eqb n : forall (x y : T n), eqb x y = true <-> (val x = val y).
Proof. 
  intros. unfold eqb. rewrite <- Z.compare_eq_iff. destruct (x?=y); simpl; intuition congruence. 
Qed. 

Lemma le_transitive n :  forall (x y z : T n), le x y = true -> le y z = true -> le x z = true.
Proof.
  intros. rewrite zify_le in *. omega. 
Qed. 

Lemma le_total  n : forall x y : T n, le x y = true \/ le y x = true. 
Proof. 
  intros; repeat rewrite zify_le in *. omega. 
Qed. 

Lemma le_antisym n : forall x y : T n,  le x y = true -> le y x = true -> x = y. 
Proof. 
  intros; repeat rewrite zify_le in *. apply unsigned_inj. unfold unsigned in *. omega. 
Qed.

Lemma le_is_lt_or_eq n : forall x y :T n, le x y = (lt x y || eqb x y)%bool.
Proof. 
  intros. 
  rewrite Bool.eq_iff_eq_true; rewrite Bool.orb_true_iff. 
  rewrite zify_le, zify_lt, zify_eqb. omega. 
Qed. 

Add Rec LoadPath "./" as Synthesis.
Require Import Consider. 

Instance reflect_le_Z {n} (x y : T n): Reflect (le x y) (val x <= val y) (val y < val x).
Proof.
  destruct (le x y)eqn:H; constructor.
  rewrite zify_le in H. auto. 
  rewrite <- zify_lt. unfold lt. unfold zlt. unfold le,zle in *.   
  replace (y ?= x) with (CompOpp (x ?= y)). destruct (x ?= y); try discriminate; reflexivity.
  clear. rewrite Zcompare_antisym. reflexivity.
Qed.

Instance reflect_lt_Z {n} (x y : T n): Reflect (lt x y) (val x < val y) (val y <= val x).
Proof.
  destruct (lt x y)eqn:H; constructor.
  rewrite zify_lt in H. auto. 
  rewrite <- zify_le. unfold lt, zlt, le, zle in *.  
  replace (y ?= x) with (CompOpp (x ?= y)). destruct (x ?= y); try discriminate; reflexivity.
  clear. rewrite Zcompare_antisym. reflexivity.
Qed.

Instance reflect_eqb_Z {n} (x y : T n): Reflect (eqb x y) (val x = val y) (val y <> val x).
Proof.
  destruct (eqb x y)eqn:H; constructor.
  rewrite zify_eqb in H. auto. 
  rewrite <- zify_eqb. unfold eqb in *.
  replace (y ?= x) with (CompOpp (x ?= y)). destruct (x ?= y); try discriminate; reflexivity.
  clear. rewrite Zcompare_antisym. reflexivity.
Qed.

   

Fixpoint power2 n : nat := 
  match n with 
    | 0 => 1
    | S n => power2 n + power2 n
  end%nat. 

Lemma Z'of_nat_power2 k : Z.of_nat (power2 k) = two_power_nat k. 
Proof. 
  induction k. reflexivity. 
  simpl. rewrite two_power_nat_S.  rewrite Nat2Z.inj_add. rewrite IHk.  ring. 
Qed. 

Lemma not_eqb n : forall p q, (p < power2 n)%nat -> (q < p)%nat -> eqb (repr n (Z.of_nat p)) (repr n (Z.of_nat q)) = false. 
Proof. 
  intros. 
  destruct (eqb (repr n (Z.of_nat p)) (repr n (Z.of_nat q))) eqn:H'; intros; trivial. 
  exfalso. 
  rewrite eqb_correct in H'. 
  unfold repr in H'. injection H'. clear H'. intros H'. 
  rewrite ? Zmod_small in H' by (clear H'; rewrite <- Z'of_nat_power2; zify; omega).
  zify; omega. 
Qed. 
