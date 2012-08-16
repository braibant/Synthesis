Require Import Common Core Front ZArith. 

Fixpoint pow2 k := (match k with O => 1 | S p => pow2 p + pow2 p end)%nat.

Notation "[2^ n ]" := (pow2 n). 

Section s. 
  
  Variable V : type -> Type. 
  Notation "'DOT' << p , g , s , t >> <- x ; f" := 
  (( 
      DO p <- RETURN (Efst _ _ _ (!x)%expr);
      DO x2 <- RETURN (Esnd _ _ _ (!x)%expr);
      DO g <- RETURN (Efst _ _ _ (!x2)%expr);
      DO x3 <- RETURN (Esnd _ _ _ (!x2)%expr);
      DO s <- RETURN (Efst _ _ _ (!x3)%expr);
      DO x4 <- RETURN (Esnd _ _ _ (!x3)%expr);
      DO t <- RETURN (Efst _ _ _ (!x4)%expr); f
)%action
  ) (at level 80,  right associativity) : action_scope. 
  
  Notation low x := ( Ebuiltin (BI_low _ _) ([x])%dlist). 
  Notation high x := ( Ebuiltin (BI_high _ _) ([x])%dlist). 
  Notation combineLH x y := ( Ebuiltin  (BI_combineLH _ _) (x :: [ y])%dlist). 
  Notation "[< a ; b ; c ; d >]" := (Etuple _ _ ([a;b;c;d])%dlist) : expr_scope. 

  Open Scope Z_scope. 
  Definition add Phi n (x : V (Tint [2^ n])) (y : V (Tint [2^ n])) : 
    action Phi V (Ttuple [Tbool; Tbool; Tint [2^ n]; Tint [2^ n]]). 
  refine (
      let fix add n (x : V (Tint [2^ n])) (y : V (Tint [2^ n]))  := 
          match n 
             return 
             V (Tint [2^ n]) ->  V (Tint [2^ n]) ->  action Phi V (Ttuple [Tbool; Tbool; Tint [2^ n]; Tint [2^ n]])
          with 
            | 0%nat => fun x y =>(RETURN [< (!x = #i 1) || (!y = #i 1) ; (!x = #i 1) && (!y = #i 1); !x + !y; !x + !y + #i 1 >])%expr
            | S n => fun x y =>
      (DO xL <- RETURN ((low (!x))%expr);
      DO xH <- RETURN ((high (!x))%expr);
      DO yL <- RETURN ((low (!y))%expr);
      DO yH <- RETURN ((high (!y))%expr);
      DO rL <- add _ xL yL;
      DO rH <- add _ xH yH;
      DOT << pL, gL, sL, tL >> <- rL; 
      DOT << pH, gH, sH, tH >> <- rH; 
      DO sH' <- RETURN (Emux _ _ (!gL) (!tH) (!sH))%expr;
      DO tH' <- RETURN (Emux _ _ (!pL) (!tH) (!sH))%expr;
      DO pH' <- RETURN (!gH || (!pH && !gH))%expr;
      DO gH' <- RETURN (!gH || (!pH && !gL))%expr;
      RETURN ([< !pH'; !gH'; combineLH (!sL) (!sH') ; combineLH  (!tL) (!tH') >])%expr
)%action
          end x y in add n x y).

  Defined.
End s. 

Definition test n : 
  Action ([Treg (Tint [2^ n]); Treg (Tint [2^ n])])%list
         (Ttuple [ B; B; W [2^n]; W [2^n]])%list. 
intros V. 
refine
    (DO x <- read [: var_0];
     DO y <- read [: var_S (var_0)];
     add V _ n x y
    )%action. 
Defined. 
Require Compiler. 
Require Import FirstOrder. 
Eval vm_compute in do r <- (Compiler.copt _ _  (test 3)); Some (List.length (bindings _ _ r)). 
Eval vm_compute in List.length (bindings _ _ (Compiler.Fo_CP_compile _ _  (test 3))). 
(* Definition test_real n s := *)
(*    Front.Eval _ s _ (test n) (Diff.init _).  *)

(* Definition ty n := (eval_state [Treg (W [2^n]); Treg (W [2^n])])%type.  *)
(* Definition x n a b : ty n := *)
(*   let a := Word.repr _ a : eval_sync (Treg (W [2^n])) in *)
(*     let b := Word.repr _ b : eval_sync (Treg (W [2^n])) in  *)
(*       ([a;b])%dlist.  *)
(* Eval vm_compute in test_real 6 (x 6 16 64).  *)
(* End Ex1.                              *)