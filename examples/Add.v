(** Examples.Add : A Von Neumann adder.  *)
Require Import Common Core Front ZArith. 

Fixpoint pow2 k := (match k with O => 1 | S p => pow2 p + pow2 p end)%nat.

Notation "[2^ n ]" := (pow2 n). 

(** A divide and conquer adder (Von Neumann)  *)
Section s. 
  
  Variable V : type -> Type. 
  Open Scope Z_scope.  
  Fixpoint add {Phi} n (x : expr V (Tint [2^ n])) (y : expr V (Tint [2^ n])) 
    :        action Phi V (Ttuple [Tbool; Tbool; Tint [2^ n]; Tint [2^ n]]) := 
    match n 
       return 
       expr V (Tint [2^ n]) -> 
       expr V (Tint [2^ n]) ->  
       action Phi V (Ttuple [Tbool; Tbool; Tint [2^ n]; Tint [2^ n]])
    with 
      | 0%nat => fun x y => 
                ret [tuple ((x = #i 1) || (y = #i 1)), (* propagate *)
                     ((x = #i 1) && (y = #i 1)),       (* generate *)
                     x + y,                            (* s *)
                     x + y + #i 1 ]%expr               (* t *)
      | S n => fun x y => 
                (
                  do xL <~ low  x;
                  do xH <~ high x; 
                  do yL <~ low  y; 
                  do yH <~ high y; 
                  do rL <- add n xL yL; 
                  do rH <- add n xH yH; 
                  do (pL, gL, sL, tL) <~ rL;
                  do (pH, gH, sH, tH) <~ rH;
                  do sH' <~ (Emux (gL) (tH) (sH))%expr;
                  do tH' <~ (Emux (pL) (tH) (sH))%expr;
                  do pH' <~ (gH || (pH && pL))%expr;
                  do gH' <~ (gH || (pH && gL))%expr;
                  ret [tuple pH', 
                       gH', 
                       combineLH sL sH', 
                       combineLH tL tH']
                )                                     
          end%expr%action x y.  
End s. 

Arguments Front.Close {Var} Phi {T U} c.

Definition generator n : Action ([Tinput (Tint [2^n]); Tinput (Tint [2^n])]%list) (Ttuple [ B; B; Int [2^n]; Int [2^n]])%list. 
  intros V. 
  apply (Front.Close ([Tinput (Tint [2^n])]%list)). 
  intros x.
  apply (Front.Close ([]%list)).
  intros y. 
  apply (add _ _ (Evar x) (Evar y)) . 
Defined.
  