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

Definition eq {n} : T n -> T n -> bool := 
  fun x y => 
    (match val x ?= val y with Eq => true | _ => false end) .

Lemma eq_correct {n} : forall x y : T n, eq x y = true -> x = y. 
Proof. 
  destruct x; destruct y. unfold eq; simpl.  
  case_eq (val0 ?= val1); intros; simpl. 
  apply Zcompare_Eq_eq in H. subst.  
  apply unsigned_inj. simpl; auto. 
  discriminate. 
  discriminate. 
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
