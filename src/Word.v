Require Export ZArith. 

Notation "[2^ n ]" := (two_power_nat n). 
(** Implementation of parametric size machine words.  *)

Record T n := mk { val :> Z ; 
                   range : (0 <= val < two_power_nat n)%Z}. 
Arguments val {n} _. 
Arguments range {n} _. 

Definition unsigned {n} (x : T n) : nat := Zabs_nat (val x).

Open Scope Z_scope. 

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
Definition minus {n} : T n -> T n -> T n := fun x y => repr n (x - y). 
Definition mult {n} : T n -> T n -> T n := fun x y => repr n (x * y).  
Definition eq {n} : T n -> T n -> bool := 
  fun x y => 
    (match val x ?= val y with Eq => true | _ => false end) .

Definition lt {n} : T n -> T n -> bool :=
  fun x y => 
    (match val x ?= val y with Lt => true | _ => false end) .
