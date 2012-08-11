Require Import Common. 
Require Core. 

Require ZArith. Open Scope Z_scope.
Module  Ex2. 
  Require Import Core Front. 
  
  Section t. 
    Variable n : nat. 
    Notation NUM := ( (Tint n)). 
    Notation VAL := ( (Tbool)) (only parsing). 
    Definition Phi : state := (Treg VAL :: Treg NUM  :: Treg NUM :: nil)%list. 
    
    Notation c := (var_0 : var Phi (Treg VAL)).
    Notation r1 := (var_S (var_0) : var Phi (Treg NUM)).  
    Notation r2 := (var_S (var_S (var_0)) : var Phi (Treg NUM)).  
    Open Scope action_scope. 
    Definition iterate : Action Phi Tunit. intros V.
    refine (DO X <- read [: c]; 
            WHEN ( !X); 
            DO A <- read [: r1]; 
            DO B <- read [: r2];
            WHEN (!B <= !A); 
            DO _ <- (write [: r1 <- (!A - !B)]);  
            RETURN #Ctt
           ). 
    Defined. 
    
    Definition done : Action Phi Tunit. intros V. 
    refine (DO X <- read [: c]; 
            WHEN (!X); 
            DO A <- read [: r1]; 
            DO B <- read [: r2];
            WHEN (!A < !B); 
            DO _ <- (write [: c <- #b false]);  
            RETURN #Ctt
           ). 
    Defined. 
    
    Definition mod : Action Phi Tunit := fun V => OrElse _ _ _ (iterate _) (done _). 

    Inductive Ty : Type :=
    | RET : Word.T n -> Ty
    | ST : Word.T n -> Word.T n -> Ty. 
    Hint Unfold Phi. 

    Program Definition start (x : Ty) : eval_state Phi :=
      match x with 
        | RET a => 
             [false; a; a] 
        | ST a b => 
            [true; a; b]
      end%dlist. 
        
    Definition finish (x : eval_state Phi) : Ty :=
      let c := DList.hd x in 
        let a  := DList.hd (DList.tl x) in 
          let b := DList.hd (DList.tl (DList.tl x)) in                
            match c with 
              | true => ST a b
              | false => RET a
            end.
    
    Definition st0 x y := start (ST (Word.repr n x) (Word.repr n y)). 
    
    Fixpoint iter {A} (f : A -> A) n :=  
      match n with 
        | 0 => id
        | S n => fun x => f (iter f n x)
      end%nat. 
    
    Definition show start k := iter (fun st => Next _ st mod) k start. 
    
  End t. 
  
  Eval compute in show 16 (st0 16 17 3) 7. 
End Ex2. 
