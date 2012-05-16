Require Export String. 
Require Vector. 

Notation "'do' X <- A ; B" := (match A with Some X => B | None => None end)
  (at level 200, X ident, A at level 100, B at level 200). 
Notation "'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200). 

Axiom admit : forall {X} , X. 

Definition ident := string. 

Definition comp {A B C} (f : B -> C) (g : A -> B) := fun (x : A) => f (g (x)). 
Notation "f ∘ g" := (comp f g) (at level 40).

Notation "[ ]" := nil : list_scope.
Notation "t :: q" := (cons t q) : list_scope. 
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..)%list : list_scope.


Section var.   
  Variable T : Type. 
  Inductive var : list T -> T -> Type :=
  | var_0 : forall E t , var (cons t E) t
  | var_S : forall E t t' , var E t' -> var (cons t E) t'. 

  Variable eval_type : T -> Type. 

  Fixpoint eval_env E : Type :=
    match E with 
        nil => unit
      | cons t q => (eval_type t * eval_env q)%type
    end. 

  Fixpoint get E t (v: var E t): eval_env E -> eval_type t :=
    match v with 
      | var_0  _ _ => fun e => (fst e)
      | var_S _ _ _ v => fun e => get _ _ v (snd e)
    end. 

  Fixpoint append_envs E F : eval_env E -> eval_env F -> eval_env (List.app E F) :=
    match E with 
      | nil => fun _ (x : eval_env F) => x 
      | cons t q => fun (X : eval_type t * eval_env q) Y => 
                     let (A,B) := X in (A, append_envs q F B Y)
    end. 
  Fixpoint set E t (v : var E t) : eval_type t ->  eval_env E -> eval_env E :=
    match v  with 
      | var_0 _ _ => fun x e => (x, snd e)
      | var_S _ _ _ v => fun x e => (fst e, set _ _ v x (snd e))
    end. 

  Fixpoint var_lift E F t (v : var E t) : var (E++F) t :=
    match v with 
        var_0 E' t'=> var_0 (E' ++ F) t'
      | var_S E' s' s'' v' => var_S (E' ++ F ) s' s'' (var_lift E' F s'' v') 
    end. 
End var. 

Arguments var {T} _ _. 
Arguments var_0 {T} {E} {t}. 
Arguments var_S {T} {E} {t} {t'} _. 
Arguments get {T eval_type} E t _ _. 
Arguments append_envs {T eval_type} E F _ _. 
Arguments eval_env {T} _ _ .  
Arguments var_lift {T E F t} v. 

Module Abstract. 
  Record T :=
    {
      carrier :> Type;
      eqb : carrier -> carrier -> bool;
      lt  : carrier -> carrier -> bool
    }. 
End Abstract. 

Require Export ZArith. 

(** Implementation of parametric size machine words.  *)
Module Word. 
  
  Record T n := mk { val :> Z ; 
                     range : (0 <= val < two_power_nat n)%Z}. 
  Arguments val {n} _. 
  Arguments range {n} _. 
  
  Definition unsigned {n} (x : T n) : nat := Zabs_nat (val x).

  Notation "[2^ n ]" := (two_power_nat n). 
  
  Open Scope Z_scope. 
  
  Lemma mod_in_range n:
    forall x, 0 <= Zmod x [2^ n] < [2^ n] .
  Proof.
    intro.
    apply (Z_mod_lt x).
    reflexivity. 
  Qed.
  
  Definition repr n (x: Z)  : T n := 
    mk n (Zmod x [2^ n]) (mod_in_range n x ).
  

  Definition add {n} : T n -> T n -> T n := fun x y => repr n (x + y ). 
  Definition minus {n} : T n -> T n -> T n := fun x y => repr n (x - y). 
  Definition mult {n} : T n -> T n -> T n := fun x y => repr n (x * y).  
  Definition eq {n} : T n -> T n -> bool := 
    fun x y => 
      (match val x ?= val y with Eq => true | _ => false end) .

  Definition lt {n} : T n -> T n -> bool :=
    fun x y => 
      (match val x ?= val y with Lt => true | _ => false end) .

End Word. 

Notation "<: val 'as' 'int' n :>" := (Word.mk n val _). 

Fixpoint lt_nat_bool n m : bool :=
  match n,m with 
    | 0, S _ => true
    | S n, S m => lt_nat_bool n m 
    | _, _ => false
  end. 


Module FIFO. 
  Section t. 
    Definition T (n : nat) X:= list X. 

    Context {X : Type}. 
    Definition push {n} x (q : T n X) : T n X:=           
      List.app q (cons x nil). 
        
    Definition first {n} (q : T n X) : option X := 
      match  q with 
        | nil => None
        | cons t q => Some t
      end. 
    
    Definition pop {n} (q : T n X) := 
      match q with 
          | nil => None
          | cons t q => Some q
      end.

    Definition isempty {n} (q : T n X) :=
      match q with 
          | nil => true
          | _ => false
      end. 

    Definition isfull {n} (q : T n X) := 
      negb (lt_nat_bool (List.length q) n). 
    
    Definition clear {n} (q : T n X) : T n X:= nil. 
  End t. 
End FIFO. 

Module Regfile. 
    
  
  Definition T (size : nat) (X : Type) := Vector.vector X size.  
    
  Definition empty size X (el : X ): T size X := Vector.empty X size el.  
  Definition get {size X} (v : T size X) (n : nat) := 
    Vector.get _ _ v n. 
  
  Definition set  {size X} (v : T size X) (addr : nat) (el : X) : T size X :=
    Vector.set _ _ v (addr)%nat el. 
  
  Definition of_list {X : Type} (l : list X) : T (List.length l) X :=
    Vector.of_list _ l. 

  Definition of_list_pad {X} n (default : X) (l : list X) : T n X := 
    Vector.of_list_pad _ n default l.  

End Regfile. 

(* The base types, that exist in every language. These types should have:
   - decidable equality; 
   - default element (to initialize the arrays)
 *)
Inductive type0 : Type :=
| Tunit : type0 
| Tbool: type0 
| Tint: nat -> type0
| Tabstract : ident -> Abstract.T -> type0. 

Fixpoint eval_type0 st : Type := 
  match st with 
    | Tunit => unit
    | Tbool => bool
    | Tint n => Word.T n
    | Tabstract _ t => Abstract.carrier t
  end. 

Definition eval_type0_list l : Type := eval_env eval_type0 l. 

(** Operations on types *)
Section type_ops. 
  
  Definition eqb_bool (b1 b2: bool)  :=
    match b1,b2 with 
      | true, true => true
      | false, false => true
      | _,_ => false
    end. 
  
  Fixpoint type0_eq(t : type0) : eval_type0 t -> eval_type0 t -> bool :=
    match t with 
      | Tunit => fun _ _  => true
      | Tint n => @Word.eq n
      | Tbool  => eqb_bool 
      | Tabstract _ t => Abstract.eqb t
    end. 
  
  
  Definition ltb_bool a b :=
    match a, b with
      | false, true => true
      | _, _ => false
    end. 
  
  Fixpoint type0_lt (bt : type0) : eval_type0 bt -> eval_type0 bt -> bool :=
    match bt with
      | Tunit => fun _ _  => true
                              
      | Tbool => ltb_bool 
      | Tint n => @Word.lt n
      | Tabstract _ t => Abstract.lt t
    end. 
End type_ops. 

 
Record signature T (E : T -> Type) := mk_signature
  {
    args : list T;
    res : T; 
    value :> eval_env E args -> E res
  }. 

Arguments mk_signature {T E} args res value. 
Arguments args {T E} s. 
Arguments res {T E} s. 
Arguments value {T E} s _. 

(* could it be a primitive with an empty set of arguments ? *)
Definition constant T (E : T -> Type) (ty : T) := E ty. 

Arguments constant {T E} ty. 

Notation signature0 := (signature type0 eval_type0). 
Notation constant0 := (@constant type0 eval_type0). 

Definition Cbool b : constant0 Tbool := b. 
Definition Cword {n} x : constant0 (Tint n) := (Word.repr _ x). 

Notation B := Tbool. 
Notation W n := (Tint n).

Inductive builtin : list type0 -> type0 -> Type :=
| BI_external :  forall (s : signature0), builtin (args s) (res s)
| BI_andb : builtin (B :: B :: nil)%list  B
| BI_orb  : builtin (B :: B :: nil)%list  B
| BI_xorb : builtin (B :: B :: nil)%list  B
| BI_negb : builtin (B  :: nil)%list  B
                    
(* "type-classes" *)
| BI_eq   : forall t, builtin (t :: t :: nil)%list B
| BI_lt   : forall t, builtin (t :: t :: nil)%list B
                         
(* integer operations *)
| BI_plus  : forall n, builtin (W n :: W n :: nil)%list (W n)
| BI_minus : forall n, builtin (W n :: W n :: nil)%list (W n). 

(* applies a binary function to two arguments *)
Definition bin_op {a b c} (f : eval_type0 a -> eval_type0 b -> eval_type0 c) 
  : eval_type0_list (a :: b :: nil)%list -> eval_type0 c :=
  fun X => match X with (x,(y, _)) => f x y end. 

(* applies a unary function to one arguments *)
Definition un_op {a b} (f : eval_type0 a -> eval_type0 b) 
  : eval_type0_list (a :: nil) -> eval_type0 b :=
  fun X => match X with (x,_) => f x end. 

  (* denotation of the builtin functions *)
Definition builtin_denotation (dom : list type0) ran (f : builtin dom ran) : 
  eval_type0_list dom -> eval_type0 ran :=
  match f with
    | BI_external s => value s
    | BI_andb => @bin_op B B B andb
    | BI_orb =>  @bin_op B B B orb
    | BI_xorb => @bin_op B B B xorb
    | BI_negb =>  @un_op B B negb
    | BI_eq t => @bin_op t t B (type0_eq t)
    | BI_lt t => @bin_op t t B (type0_lt t)
    | BI_plus n => @bin_op (W n) (W n) (W n) (@Word.add n)
    | BI_minus n => @bin_op (W n) (W n) (W n) (@Word.minus n)
  end. 


Definition relation A := A -> A -> Prop. 
Definition union {A} (R S : relation A) := fun x y => R x y \/ S x y. 
