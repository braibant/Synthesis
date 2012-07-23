Require Core Front RTL Flat CSE FirstOrder. 


Definition compile Phi t  (a : forall Var, Front.action Phi Var t) : forall Var, Flat.block Phi Var t.  
intros.
apply Flat.compile. 
apply RTL.nblock_to_block. 
apply RTL.compile. 
apply a. 
Defined. 


Lemma compile_correct (Phi : Core.state) t a :
  let block := compile Phi t a in 
  forall st Delta, 
  Flat.eval_block Phi st t (block Core.eval_type) Delta =
     Front.Sem.eval_action (a Core.eval_type) st Delta. 
Proof. 
  intros. 

  rewrite <- RTL.CPS_compile_correct.        
  rewrite <- RTL.nblock_compile_correct.
  rewrite <- Flat.compile_correct. 
  unfold block. unfold compile. 
  reflexivity. 
Qed. 

Print Assumptions compile_correct. 

Definition fo_compile Phi t  (a : forall Var, Front.action Phi Var t) :  FirstOrder.block Phi t.  
intros.
apply FirstOrder.compile. 
apply Flat.compile. 
apply RTL.nblock_to_block. 
apply RTL.compile. 
apply a. 
Defined. 


Definition fo_cse_compile Phi t  (a : forall Var, Front.action Phi Var t) :  FirstOrder.block Phi t.  
intros.
apply FirstOrder.compile. 
apply CSE.cse_block. 
apply Flat.compile. 
apply RTL.nblock_to_block. 
apply RTL.compile. 
apply a. 
Defined. 

Print Opaque Dependencies fo_cse_compile.