Add Rec LoadPath "./" as Synthesis.


Require Core Front IR RTL CSE CP FirstOrder.


Definition fesic Phi t  (a : forall Var, Front.action Phi Var t) : RTL.Block Phi t :=
  let x := IR.Compile Phi  t a in
  let x := RTL.Compile Phi t x in 
  let x := CSE.Compile Phi t  x in    
  CP.Compile Phi t x.                 (* We use the notation BDD.compile in the paper here *)




Axiom HWF : forall Phi t p, RTL.WF Phi t p. 
Lemma fesic_correct (Phi : Core.state) t a :
  let block := fesic Phi t a in 
  forall st, 
    RTL.Next Phi st t block =
    Front.Next Phi st a. 
Proof.
  unfold fesic. intros. 
  rewrite CP.Compile_correct by apply HWF.  
  rewrite CSE.Compile_correct by apply HWF. 
  rewrite RTL.Compile_correct. 
  rewrite IR.Compile_correct. 
  reflexivity. 
Qed. 

Definition Fesic Phi t src := 
  let x := (fesic Phi t src) in 
  let x := FirstOrder.compile Phi t (x _ ) in 
  Some x.
 
