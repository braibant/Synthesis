Require Import FMapPositive.
Require Import NArith. 
Require Import ZArith. 

Require Word. 

Module Map := PositiveMap. 

Section t. 
  Record T (size : nat) X := mk
    {
      body : Map.t X;
      zero : X  
    }. 
  
  Arguments body {size X} _. 
  Arguments zero {size X} _. 

  Variable X : Type.

  Definition set {n} (v : T n X) (adr: Word.T n) (x : X) : T n X :=
    match Z.to_N (Word.val adr)  with 
        | N0 => mk _ _ (body v) x
        | Npos p => mk _ _ (Map.add p x (body v)) (zero v)
        end. 

  Definition get {n} (v : T n X) (adr: Word.T n) : X :=
    match Z.to_N (Word.val adr)  with 
        | N0 => zero v
        | Npos p => 
            match Map.find p  (body v) with 
                | None => zero v
                | Some x => x
        end end. 
  
  Definition empty n el : T n X := mk _ _ (Map.empty _) el.

End t. 

Arguments get {X n} _ _. 
Arguments set {X n} _ _ _. 
             
    

