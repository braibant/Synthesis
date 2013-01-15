Add Rec LoadPath "./" as Synthesis. 
Require Core Front IR RTL CSE CP FirstOrder.

(** Putting it all together: the final compiler  *)

Definition fesic Phi t  (a : forall Var, Front.action Phi Var t) : RTL.Block Phi t :=
  let x := IR.Compile Phi  t a in
  let x := RTL.Compile Phi t x in 
  let x := CSE.Compile Phi t  x in
  let x := CP.Compile Phi t x in                  (* We use the notation BDD.compile in the paper here *)
  let x := CSE.Compile Phi t  x in
  x.


(** The proof of the compiler relies on the so-called PHOAS axiom that
states that programs are really parametric in the choice of the
representations of variables. Past papers on PHOAS discuss the use
of this axiom: 
- http://adam.chlipala.net/papers/PhoasICFP08/ 
- http://adam.chlipala.net/papers/ImpurePOPL10/

Note that we could alleviate our use of this axiom by proving that
compilation preserves a notion of well-formedness, and that every
source program is well-formed. *)

Axiom HWF : forall Phi t p, RTL.WF Phi t p. 
Lemma fesic_correct (Phi : Core.state) t a :
  let block := fesic Phi t a in 
  forall st, 
    RTL.Next Phi st t block =
    Front.Next Phi st a. 
Proof.
  unfold fesic. intros. 
  repeat 
    (first 
    [
      rewrite CSE.Compile_correct by apply HWF|
      rewrite CP.Compile_correct by apply HWF]).

  rewrite RTL.Compile_correct. 
  rewrite IR.Compile_correct. 
  reflexivity. 
Qed. 

Definition Fesic Phi t src := 
  let x := (fesic Phi t src) in 
  let x := FirstOrder.compile Phi t (x _ ) in 
  Some x.
 
