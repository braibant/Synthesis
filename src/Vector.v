Require Import FMapPositive.
Require Import NArith. 
Require Import ZArith. 

Add Rec LoadPath "." as Synthesis. 
Require Word. 

(** Vectors (that is, arrays)  *)
Section t. 
  Variable length : nat.
  Variable X  : Type. 
  Definition T := Word.T length ->  X. 

  Definition set  (v : T) (j: Word.T length) (x: X) : T :=
    fun i => if Word.eqb i j then x else v i. 

  Definition get (v: T) (i : Word.T length) : X :=
    v i.

  Lemma gso (v : T)  i j x:
    Word.eqb i j = false -> 
    get (set v i x) j = get v j.
  Proof. 
    intros; unfold get, set. simpl. 
    replace (Word.eqb j i) with (Word.eqb i j). rewrite H. auto.
    rewrite (Bool.eq_iff_eq_true). rewrite ? Word.eqb_correct. intuition.
  Qed. 

  Lemma gss v i j x: 
    Word.eqb i j = true -> 
    get (set v i x) j = x. 
  Proof. 
    unfold get, set. intros. 
    replace (Word.eqb j i) with (Word.eqb i j). rewrite H. auto.
    rewrite (Bool.eq_iff_eq_true). rewrite ? Word.eqb_correct. intuition.
  Qed.
End t.

Arguments get {length X} _ _. 
Arguments set {length X} _ _ _ _. 
             
    

