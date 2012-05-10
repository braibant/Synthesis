Require Import Common Core. 

Section t. 
  Variable n : nat. 
  Notation NUM := (Tlift (Tint n)). 
  Notation VAL := (Tlift (Tbool)) (only parsing). 
  Definition Phi : state := Treg VAL :: Treg NUM  :: Treg NUM :: nil. 
  
  Definition iterate : Action Phi Unit. intros V.
  set (c := var_0 : var Phi (Treg VAL)). 
  set (r1 := var_S (var_0) : var Phi (Treg NUM)).  
  set (r2 := var_S (var_S (var_0)) : var Phi (Treg NUM)). 
  refine (DO X <- read [: c]; 
          WHEN ( !X); 
          DO A <- read [: r1]; 
          DO B <- read [: r2];
          WHEN (!B <= !A); 
          DO _ <- (write [: r1 <- (!A - !B)]);  
          (* DO _ <- (write [: r2 <- (!B)]);   *)
          RETURN #Ctt
         ). 
  Defined. 
  
  Definition done : Action Phi Unit. intros V. 
  set (c := var_0 : var Phi (Treg VAL)). 
  set (r1 := var_S (var_0) : var Phi (Treg NUM)).  
  set (r2 := var_S (var_S (var_0)) : var Phi (Treg NUM)). 
  refine (DO X <- read [: c]; 
          WHEN (!X); 
          DO A <- read [: r1]; 
          DO B <- read [: r2];
          WHEN (!A < !B); 
          DO _ <- (write [: c <- #b false]);  
          (* DO _ <- (write [: r1 <- !A ]);   *)
          RETURN #Ctt
         ). 
  Defined. 
  
  Definition T : TRS := mk_TRS Phi (iterate :: done :: nil). 
  
  Inductive Ty : Type :=
  | RET : Word.T n -> Ty
  | ST : Word.T n -> Word.T n -> Ty. 
  
  Definition start (x : Ty) : eval_state Phi :=
    match x with 
      | RET a => (false, (a, (a, tt)))
      | ST a b => (true, (a, (b, tt)))
    end.
  
  Definition finish (x : eval_state Phi) : Ty :=
    match x with 
      | (c,(a,(b,_))) => 
          match c with 
            | true => ST a b
            | false => RET a
          end
    end. 
  
  Definition st0 x y := start (ST (Word.repr n x) (Word.repr n y)). 
  
  Definition finish' x := match x with None => None | Some x => Some (finish x) end. 
End t. 

Eval compute in finish' 16 (run_unfair (T 16) 10 (st0 16 17 3)). 
