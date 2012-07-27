Require Import Common. 

Module WithFailure. 
Record T (I O sigma : Type) :=
  {
    lambda : sigma -> O;
    delta : sigma -> I -> option sigma 
  }.

Arguments lambda {I O sigma} t _.
Arguments delta {I O sigma} t _ _.

Fixpoint iterate {I O sigma} (M : T I O sigma) x (ins : nat -> I) k : option sigma := 
  match k with 
    | 0 => x
    | S n => 
        do st <-  (iterate M x ins n);
        (delta M) st (ins n)
  end. 

Definition outputs {I O sigma} (M : T I O sigma) x (ins : nat -> I) k : option O :=
  do st <- iterate M x ins k;
  Some ((lambda M) st).

End WithFailure. 

Module Relation. 
  Record T (I O sigma : Type) :=
    {
      lambda : sigma -> O;
      delta : sigma -> I -> sigma -> Prop
    }.

  Arguments lambda {I O sigma} t _.
  Arguments delta {I O sigma} t _ _ _.
  
  Fixpoint iterate {I O sigma} (M : T I O sigma) (ins : nat -> I) k : relation sigma := 
    match k with 
      | 0 => fun x y  => True 
      | S n => 
          fun x z => 
            exists y, 
          iterate M ins n x y /\ 
                  (delta M) x (ins n) z 
    end. 

End Relation. 

