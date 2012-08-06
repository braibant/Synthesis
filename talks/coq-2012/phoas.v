Inductive T : Type :=
  | Tbool
  | Tarrow : T -> T -> T. 

Section t. 

  Variable V : T -> Type. 
  Inductive term : T -> Type :=
  | Var : forall t, V t -> term t
  | Abs : forall a b, (V a -> term b) -> term (Tarrow a b)
  | App : forall a b, term (Tarrow a b) -> term a -> term b. 
End t.  

Definition Term t := forall V, term V t. 

Arguments Abs {V a b} _. 
Arguments Var {V t} _. 
Example K a b : Term (Tarrow a (Tarrow b a))  := fun V => Abs (fun x => Abs (fun y => Var x)). 