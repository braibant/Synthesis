Require Import Common Core Front. 
    
Require ZArith. Open Scope Z_scope.

Section t. 
  Variable W : nat. 
  Notation NUM := (Tint W). 
  Notation STATUS := (Tfin 3). 

  Definition Phi : state := (Treg NUM :: Treg NUM  :: Treg NUM ::  nil)%list. 
    
  Notation N := (var_0 : var Phi (Treg NUM)).
  Notation M := (var_S (var_0) : var Phi (Treg NUM)).  
  Notation R := (var_S (var_S (var_0)) : var Phi (Treg NUM)).  
  
  Notation "'If' c { b1 } 'else' { b2 }" := 
  (OrElse _ _ _ (WHEN (c)%expr; b1) b2) 
    (no associativity, at level 95, c at level 0). 
  
  Definition mult : Action Phi Tunit. intros V. 
  refine ( DO n   <- read [: N ];
           DO m   <- read [: M ];
           DO acc <- read [: R ];
           If (! m = #i 0) 
              { 
                RETURN #Ctt 
              }
           else 
             { 
               DO _ <- (write [: M <- (!m - #i 1)]);
               DO _ <- (write [: R <- (!acc + !n)]);
               RETURN #Ctt
             } 
         )%action. 
  Defined.
End t. 

Require Compiler. 
Require Import FirstOrder Core.
Eval vm_compute in Compiler.Fo_compile (Phi 5) _ (mult 5). 

