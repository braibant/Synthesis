Require Import Common Core Front ZArith. 

Fixpoint pow2 k := (match k with O => 1 | S p => pow2 p + pow2 p end)%nat.

Notation "[2^ n ]" := (pow2 n). 

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
                ret [tuple ((x = #i 1) || (y = #i 1)), 
                     ((x = #i 1) && (y = #i 1)), 
                     x + y, 
                     x + y + #i 1 ]%expr
      | S n => fun x y => 
                (
                  do xL <~ low  x;
                  do xH <~ high x; 
                  do yL <~ low  y; 
                  do yH <~ high y; 
                  do rL <- add n xL yL; 
                  do rH <- add n xH yH; 
                  do (pL, gL, sL, tL) <- rL;
                  do (pH, gH, sH, tH) <- rH;
                  do sH' <~ (Emux (gL) (tH) (sH))%expr;
                  do tH' <~ (Emux (pL) (tH) (sH))%expr;
                  do pH' <~ (gH || (pH && gH))%expr;
                  do gH' <~ (gH || (pH && gL))%expr;
                  ret [tuple pH', 
                       gH', 
                       combineLH sL sH', 
                       combineLH tL tH']
                )                                     
          end%expr%action x y.  
End s. 

Definition test n : 
  Action ([Treg (Tint [2^ n]); Treg (Tint [2^ n])])%list
         (Ttuple [ B; B; W [2^n]; W [2^n]])%list. 
intros V. 
refine
    (do x <- ! var_0 ;
     do y <- ! (var_S (var_0));
     add V n x y 
    )%action. 
Defined. 
Require Compiler. 
Require Import FirstOrder. 
Time Eval vm_compute in do r <- (Compiler.copt _ _  (test 5)); Some (List.length (bindings _ _ r)). 
Time Eval vm_compute in do r <- (Compiler.copt _ _  (test 6)); Some (List.length (bindings _ _ r)). 
Time Eval vm_compute in do r <- (Compiler.copt _ _  (test 7)); Some (List.length (bindings _ _ r)). 
Time Eval vm_compute in do r <- (Compiler.copt _ _  (test 8)); Some (List.length (bindings _ _ r)). 
Time Eval vm_compute in do r <- (Compiler.copt _ _  (test 9)); Some (List.length (bindings _ _ r)). 

(* Eval vm_compute in List.length (bindings _ _ (Compiler.Fo_CP_compile _ _  (test 5))).  *)
(* Definition test_real n s := *)
(*    Front.Eval _ s _ (test n) (Diff.init _).  *)

(* Definition ty n := (eval_state [Treg (W [2^n]); Treg (W [2^n])])%type.  *)
(* Definition x n a b : ty n := *)
(*   let a := Word.repr _ a : eval_sync (Treg (W [2^n])) in *)
(*     let b := Word.repr _ b : eval_sync (Treg (W [2^n])) in  *)
(*       ([a;b])%dlist.  *)
(* Eval vm_compute in test_real 6 (x 6 16 64).  *)
(* End Ex1.                              *)