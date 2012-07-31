Require Core Front RTL Flat CSE FirstOrder. 


Definition Compile Phi t  (a : forall Var, Front.action Phi Var t) : Flat.Block Phi t :=
  let x := RTL.Compile Phi  t a in
  let x := Flat.Compile Phi t x in 
  let x := CSE.Compile Phi t  x in  
        x. 

Lemma Compile_correct (Phi : Core.state) t a :
  let block := Compile Phi t a in 
  forall st Delta, 
    Flat.Eval Phi st t block Delta =
    Front.Eval Phi st t a Delta. 
Proof.
  unfold Compile. intros. 
  rewrite CSE.Compile_correct. 
  rewrite Flat.Compile_correct. 
  rewrite RTL.Compile_correct. 
  reflexivity. 
  admit. 
Qed. 

Print Assumptions Compile_correct. 

Definition Fo_compile Phi t (A : Front.Action Phi t) :  FirstOrder.block Phi t :=
  let x := Compile Phi t A in 
    FirstOrder.compile Phi t (x _ ).  
