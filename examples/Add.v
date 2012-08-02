Require Import Common Core Front. 
    
Require ZArith. Open Scope Z_scope.
Module Ex1. 
Section t. 
  Variable W : nat. 
  
  (* do x <- ! r1;if (x <> 0) then {do y <- !r2; r1 := x - 1; r2 := y + 1} else {do y <- !r2; r1 := y} *)

  Notation NUM := (Tint W). 

  Definition Phi : state := (Treg NUM :: Treg NUM  :: nil)%list. 
    
  Notation r1 := (var_0 : var Phi (Treg NUM)).
  Notation r2 := (var_S (var_0) : var Phi (Treg NUM)).  
  
  Notation "'If' c { b1 } 'else' { b2 }" := 
  (OrElse _ _ _ (WHEN (c)%expr; b1) b2) 
    (no associativity, at level 95, c at level 0). 
  
  Definition mult : Action Phi Tunit. intros V. 
  refine ( DO x   <- read [: r1 ];
           If (! x <> #i 0) 
              {
                DO y <- read [: r2 ];
                DO _ <- (write [: r1 <- !x - #i 1]);
                DO _ <- (write [: r2 <- !y + #i 1]);
                RETURN #Ctt 
              }
           else 
             {
               DO y <- read [: r2 ];
               write [: r1 <- !y]
             })%action. 
  Defined.

End t. 

Require Import FirstOrder Core.

Require  RTL. 
Notation "x :- e1 ; e2" := (RTL.telescope_bind _ _ _ _ (RTL.bind_expr _ _ _ e1) (fun x => e2)) (right associativity, at level 80, e1 at next level).  
Notation "x :- ! e1 ; e2" := (RTL.telescope_bind _ _ _  _ (RTL.bind_reg_read _ _ _  e1) (fun x => e2)) (right associativity, at level 80, e1 at next level).  
Notation "& e" := (RTL.telescope_end _ _ _  e) (right associativity, at level 80, e1 at next level).  
Notation "x @@ { l }" := (RTL.neffect_guard _ _ x l) (no associativity, at level 71). 
Notation "v := x" := (RTL.neffect_reg_write _ _ _ v x) (no associativity, at level 80). 
Eval vm_compute in RTL.compile (Phi 5) _ _ (mult 5 (fun _ => unit)). 

Notation "x 'when' b" := (RTL.effect_reg_write _ _ x b) (no associativity, at level 80). 
Eval vm_compute in RTL.Compile (Phi 5) _ (mult 5). 

Require Compiler. 
Eval vm_compute in Compiler.Fo_compile (Phi 5) _ (mult 5). 
End Ex1. 


Fixpoint pow2 k := (match k with O => 1 | S p => pow2 p + pow2 p end)%nat.

Notation "[2^ n ]" := (pow2 n). 

Section s. 
  
  Variable V : type -> Type. 


  Definition add Phi n (x : V (Tint [2^ n])) (y : V (Tint [2^ n])) : 
    action Phi V (Ttuple [Tbool; Tbool; Tint [2^ n]; Tint [2^ n]]). 
  refine (
      let fix add n (x : V (Tint [2^ n])) (y : V (Tint [2^ n]))  := 
          match n 
             return 
             V (Tint [2^ n]) ->  V (Tint [2^ n]) ->  action Phi V (Ttuple [Tbool; Tbool; Tint [2^ n]; Tint [2^ n]])
          with 
            | 0 => _
            | S n => _
          end%nat x y in add n x y); clear - add;intros x y.
  Notation "[ a ; b ; c ; d ]" := (Etuple _ _ ([a;b;c;d])%dlist) : expr_scope. 
 
  simpl in *. 

  refine (RETURN [(!x = #i 1) || (!y = #i 1) ; (!x = #i 1) && (!y = #i 1); !x + !y; !x + !y + #i 1])%expr. 

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
  refine (
      DO xL <- RETURN ((low (!x))%expr);
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
      RETURN ([!pH'; !gH'; combineLH (!sL) (!sH') ; combineLH  (!tL) (!tH') ])%expr
    )%action. 

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
Eval vm_compute in Compiler.Fo_compile _ _  (test 3). 
Definition test_real n s :=
   Front.Eval _ s _ (test n) (Diff.init _). 

Definition ty n := (eval_state [Treg (W [2^n]); Treg (W [2^n])])%type. 
Definition x n a b : ty n :=
  let a := Word.repr _ a : eval_sync (Treg (W [2^n])) in
    let b := Word.repr _ b : eval_sync (Treg (W [2^n])) in 
      ([a;b])%dlist. 
Eval vm_compute in test_real 6 (x 6 16 64). 
                            