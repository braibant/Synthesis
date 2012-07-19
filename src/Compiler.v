Require Core. 
Require RTL. 

Definition compile Phi t  (a : forall Var, Core.action Phi Var t) : forall Var, RTL.block Phi Var t.  
intros. 
apply RTL.nblock_to_block. 
apply RTL.compile. 
apply a. 
Defined. 


Lemma compile_correct (Phi : Core.state) t a :
  let block := compile Phi t a in 
  forall st Delta, 
  RTL.eval_block Phi st t (block Core.eval_type) Delta =
     Core.Sem.eval_action (a Core.eval_type) st Delta. 
Proof. 
  intros. 
  rewrite <- RTL.CPS_compile_correct.        
  rewrite <- RTL.nblock_compile_correct.
  unfold block. unfold compile. 
  reflexivity. 
Qed. 

Print Assumptions compile_correct. 

                      
        
  
