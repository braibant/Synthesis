Require Import Common DList Core Front. 
    
Require ZArith. Open Scope Z_scope.

Section t. 
  Variable W : nat. 
  Notation NUM := (Tint W). 

  Definition Phi : state := (Treg NUM :: Treg NUM  :: Treg NUM ::  nil)%list. 
    
  Notation N := (var_0 : var Phi (Treg NUM)).
  Notation M := (var_S (var_0) : var Phi (Treg NUM)).  
  Notation R := (var_S (var_S (var_0)) : var Phi (Treg NUM)).  
  
  Notation "'If' c 'then' b1 'else' b2 " := 
  (OrElse _ _ _ (WHEN (c)%expr ; b1)%action b2) 
    (no associativity, at level 200, c,b1,b2 at level 200). 
  
  Definition mult : Action Phi Tunit. intros V. 
  refine ( do n <- ! N; 
           do m <- ! M; 
           do acc <- ! R;
           ( 
           If (m = #i 0) 
           then
                ret (#Ctt)              
           else 
             (               
               do _ <- M ::= (m - (#i 1)) ;
               do _ <- R ::= (acc + n);
               ret (#Ctt))
           ))%action. 
  Defined.
  
End t. 

    
    