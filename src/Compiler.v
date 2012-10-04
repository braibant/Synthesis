Require Core Front IR RTL CSE CP FirstOrder (* DCE *). 


Definition front Phi t  (a : forall Var, Front.action Phi Var t) : RTL.Block Phi t :=
  let x := IR.Compile Phi  t a in
  let x := RTL.Compile Phi t x in 
  let x := CSE.Compile Phi t  x in  
        x. 

Definition opt Phi t (x : RTL.Block Phi t) (* :  option (FirstOrder.block Phi t) *) :=
  let x := CP.Compile Phi t x in
    (* Constant propagation may have introduced some extra sharing,
    and we may have to remove some occurences of Evar *)
  let x := CSE.Compile Phi t x in
  x. 

Axiom HWF : forall Phi t p, RTL.WF Phi t p. 
Lemma front_correct (Phi : Core.state) t a :
  let block := front Phi t a in 
  forall st Delta, 
    RTL.Eval Phi st t block Delta =
    Front.Eval Phi st t a Delta. 
Proof.
  unfold front. intros. 
  rewrite CSE.Compile_correct. 
  rewrite RTL.Compile_correct. 
  rewrite IR.Compile_correct. 
  reflexivity. 
  apply HWF. 
Qed. 

Lemma opt_correct (Phi : Core.state) t src :
  let tgt := opt _ _ src in 
  forall st Delta, 
    RTL.Eval Phi st t tgt Delta =
    RTL.Eval Phi st t src Delta. 
Proof. 
  unfold opt; intros. 
  rewrite CSE.Compile_correct by apply HWF.  
  rewrite CP.Compile_correct by apply HWF.  
  reflexivity. 
Qed.   

Definition fesic Phi t src := 
  let x := (front Phi t src) in 
  let x := FirstOrder.compile Phi t (x _ ) in 
  (* DCE.compile Phi   *) Some x.
 
Definition fesiopt Phi t x := 
  let x := opt Phi t (front Phi t x) in 
  let x := FirstOrder.compile Phi t (x _ ) in 
  (* DCE.compile Phi   *) Some x.

