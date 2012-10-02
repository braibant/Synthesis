Require Core Front IR RTL CSE CP FirstOrder (* DCE *). 


Definition Compile Phi t  (a : forall Var, Front.action Phi Var t) : RTL.Block Phi t :=
  let x := IR.Compile Phi  t a in
  let x := RTL.Compile Phi t x in 
  let x := CSE.Compile Phi t  x in  
        x. 

Lemma Compile_correct (Phi : Core.state) t a :
  let block := Compile Phi t a in 
    RTL.WF Phi t (RTL.Compile _ _(IR.Compile _ _ a)) -> 
  forall st Delta, 
    RTL.Eval Phi st t block Delta =
    Front.Eval Phi st t a Delta. 
Proof.
  unfold Compile. intros. 
  rewrite CSE.Compile_correct. 
  rewrite RTL.Compile_correct. 
  rewrite IR.Compile_correct. 
  reflexivity. 
  apply H. 
Qed. 

Print Assumptions Compile_correct. 

Definition Fo_compile Phi t (A : Front.Action Phi t) :=
  let x := Compile Phi t A in 
    FirstOrder.compile Phi t (x _ ).  


Definition Fo_CP_compile Phi t (A : Front.Action Phi t) :=
  let x := Compile Phi t A in 
  let x := CP.Compile Phi t x in 
    (* Constant propagation may have introduced some extra sharing,
    and we may have to remove some occurences of Evar *)
  let x := CSE.Compile Phi t x in 
    FirstOrder.compile Phi t (x _ ).  

Definition copt Phi t (A : Front.Action Phi t) (* :  option (FirstOrder.block Phi t) *) :=
  let x := Compile Phi t A in 
  (* let x := CP.Compile Phi t x in  *)
    (* Constant propagation may have introduced some extra sharing,
    and we may have to remove some occurences of Evar *)
  (* let x := CSE.Compile Phi t x in  *)
  let x := FirstOrder.compile Phi t (x _ ) in 
    (* DCE.compile Phi   *) Some x.
