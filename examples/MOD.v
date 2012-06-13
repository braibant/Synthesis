Require Import Common. 
Require Core TaggedUnions. 

Module Ex1. 
  Import TaggedUnions. 
  
  Section t. 
    Variable n : nat. 
    
    Definition T : type := 
      Tunion ([Int n; Ttuple [Int n; Int n]])%list.
        
    Notation MOD := (var_S var_0). 
    Notation VAL := var_0. 

    Definition Phi : state := (Treg T :: nil)%list. 
    
    Notation R := (var_0 : var Phi (Treg T)). 
    Notation "^ X " := (Econstr _ _ _ X) (at level 1, no associativity). 
    Definition iterate : Action Phi Unit. intros V.
    refine (DO R' <- read [: R ]; 
            (MATCH (!R') IN T WITH MOD OF  A , B ==>  
                  (
                    WHEN (!B <= !A);
                    DO _ <- (write [: R <- ^ MOD [< !A - !B ; !B >]]);
                    Return (#Ctt)
                  )
           )). 
    Defined. 
    
    Definition done : Action Phi Unit. intros V. 
    refine (DO R' <- read [: R];
            (MATCH (!R') IN T WITH MOD OF A, B ==> 
                   (
                     WHEN (!A < !B);
                     DO _ <- (write [: R <- ^ VAL (!A) ]);
                     Return (#Ctt)
                   )
           )). 
    Defined. 
    
    Definition This : TRS := mk_TRS Phi (iterate :: done :: nil)%list. 
    
    Inductive Ty : Type :=
    | RET : Word.T n -> Ty
    | ST : Word.T n -> Word.T n -> Ty. 
    
    Eval compute in eval_state Phi. 
    Definition start (x : Ty) : eval_state Phi :=
      match x with 
        | RET a => (inl a, tt)
        | ST a b => (inr (inl ((a,b))) , tt)
      end.

    Definition finish (x : eval_state Phi) : Ty :=
      match fst x with
        | inl t => RET t
        | inr (inl p) => ST (fst p) (snd p)
        | inr (inr f) => False_rec Ty f
      end. 
    
    Definition st0 x y := start (ST (Word.repr n x) (Word.repr n y)). 
    
    Definition finish' x := match x with None => None | Some x => Some (finish x) end. 
  End t. 
  
  Eval compute in finish' 16 (run_unfair (This 16) 10 (st0 16 17 3)). 
End Ex1. 

Module  Ex2. 
  Import Core. 
  
  Section t. 
    Variable n : nat. 
    Notation NUM := (Tlift (Tint n)). 
    Notation VAL := (Tlift (Tbool)) (only parsing). 
    Definition Phi : state := (Treg VAL :: Treg NUM  :: Treg NUM :: nil)%list. 
    
    Notation c := (var_0 : var Phi (Treg VAL)).
    Notation r1 := (var_S (var_0) : var Phi (Treg NUM)).  
    Notation r2 := (var_S (var_S (var_0)) : var Phi (Treg NUM)).  
    Open Scope action_scope. 
    Definition iterate : Action Phi Unit. intros V.
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
    
    Definition T : TRS := mk_TRS Phi (iterate :: done :: nil)%list. 
    
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
End Ex2. 
