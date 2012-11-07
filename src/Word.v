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

Definition true := repr 1 1. 
Definition false := repr 1 0. 

Definition of_bool (b: bool) : T 1 := if b then true else false.

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
