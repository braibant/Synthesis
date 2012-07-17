Require Export String. 
Require Vector. 

Definition bind {A B: Type} (f: option A) (g: A -> option B) : option B :=
  match f with
    | Some x => g x
    | None => None
  end.

Notation "'do' X <- A ; B" := (bind A (fun X => B) )
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


  Fixpoint var_lift E F t (v : var E t) : var (E++F) t :=
    match v with 
        var_0 E' t'=> var_0 (E' ++ F) t'
      | var_S E' s' s'' v' => var_S (E' ++ F ) s' s'' (var_lift E' F s'' v') 
    end. 

End var. 

Arguments var {T} _ _. 
Arguments var_0 {T} {E} {t}. 
Arguments var_S {T} {E} {t} {t'} _. 
Arguments var_lift {T E F t} v. 

Definition var_map {A B: Type} (F : A -> B) (l : list A) t (v : var l t) : var (List.map F l) (F t). 
induction v. apply var_0. 
simpl. apply var_S.   auto. 
Defined. 


Module Tuple. 
  Section t. 
    Variable T : Type. 
    Variable F : T -> Type. 

    Fixpoint of_list l : Type :=
      match l with 
          nil => unit
        | cons t q => (F t * of_list q)%type
      end. 
    
    Fixpoint app l1 l2 : of_list l1 -> of_list l2 -> of_list (List.app l1 l2) :=
      match l1 with 
        | nil => fun _ (x : of_list l2) => x 
        | cons t q => fun (X : F t * of_list q) Y => 
                       let (A,B) := X in (A, app q l2 B Y)
      end. 
    
    Fixpoint get l t (v: var l t): of_list l -> F t :=
      match v with 
        | var_0  _ _ => fun e => (fst e)
        | var_S _ _ _ v => fun e => get _ _ v (snd e)
      end. 
    
    Fixpoint set l t (v : var l t) : F t ->  of_list l -> of_list l:=
      match v  with 
        | var_0 _ _ => fun x e => (x, snd e)
        | var_S _ _ _ v => fun x e => (fst e, set _ _ v x (snd e))
      end. 
  Fixpoint init (el : forall t, F t) l : of_list l :=
    match l with 
      | nil => tt
      | cons t q => (el t, init el q)
    end. 
  End t. 
  
  Section map2. 
    Context {T : Type} {F : T -> Type} {F' : T -> Type}. 
    Variable (up : forall a,  F a -> F' a -> F' a). 
    Definition map2 l : of_list T F l -> of_list T F' l -> of_list T F' l. 
    induction l. simpl. auto. 
    simpl. intros [x xs] [y ys]. split. apply up; auto.  
    apply IHl; auto. 
    Defined. 
  End map2. 

  Section map3. 
    Context {T : Type} {F F' F'': T -> Type}.
    Variable (up : forall a,  F a -> F' a -> F'' a -> F'' a). 
    Definition map3 l : of_list T F l -> of_list T F' l -> of_list T F'' l -> of_list T F'' l. 
    induction l. simpl. auto. 
    simpl. intros [x xs] [y ys] [z zs]. split. apply up; auto.  
    apply IHl; auto. 
    Defined. 
  End map3. 
  
  Section fold. 
    Context {T B : Type} {F : T -> Type}. 
    Definition fold l (up : forall a, F a -> var l a -> B -> B): of_list T F l -> B -> B. 
    refine (let fold :=
                fix fold l  : ( forall a, F a -> var l a -> B -> B) -> of_list T F l -> B -> B :=
                match l as l' return  ( forall a, F a -> var l' a -> B -> B) -> of_list T F l' -> B -> B with
                    | nil => fun f _ acc => acc
                    | cons t q => fun f  (X : F t * of_list T F q) acc => 
                                   let (x,xs) := X in 
                                   let f' := (fun b (fb : F b) (v : var q b) => f b fb (var_S v)) in
                                     fold q f' xs (f t x var_0 acc)
                end in fold l up). 
    Defined. 
  End fold. 
  Definition fst {T F l} {t: T} : (Tuple.of_list _ F (t::l)%list) -> F t. apply fst. Defined. 
  Definition snd {T F l} {t: T} : (Tuple.of_list _ F (t::l)%list) -> Tuple.of_list _ F l. apply snd. Defined. 


End Tuple. 

Arguments Tuple.get {T F} l t _ _. 
Arguments Tuple.app {T F} l1 l2 _ _. 
Arguments Tuple.of_list {T} _ _ .  


Module ETuple. 
  Section t. 
    Variable T : Type. 
    Variable F : T -> Type. 

    Fixpoint of_list l : Type :=
      match l with 
        |  nil => unit
        | cons t q =>
            match q with 
                | nil => F t
                | cons t' q' => (F t * of_list q)%type
            end
      end. 
    

    Definition fst {t l} : of_list (t :: l) -> F t. 
    intros X. simpl in X. destruct l.  auto. destruct X. auto. 
    Defined. 
    
    Definition snd {t l} : of_list (t :: l) -> of_list l. 
    intros X. simpl in X. destruct l.  auto.  apply tt. destruct X. auto. 
    Defined. 
    
    Definition pair {t l} : F t -> of_list l -> of_list (t::l). 
    intros. simpl. destruct l. auto. auto. 
    Defined. 
    
    Definition app l1 l2 : of_list l1 -> of_list l2 -> of_list (List.app l1 l2). 
    refine (let fix app l1 l2 : of_list l1 -> of_list l2 -> of_list (List.app l1 l2) :=
                match l1 with 
                  | nil => fun _ e => e
                  | cons t q => fun X Y => 
                                let A := fst X in 
                                let B := snd X in 
                                  pair A (app _ _ B Y)
                end in app l1 l2).
    Defined. 
    
    Fixpoint get l t (v: var l t): of_list l -> F t :=
      match v with 
        | var_0  _ _ => fun e => (fst e)
        | var_S _ _ _ v => fun e => get _ _ v (snd e)
      end. 
    
    Fixpoint set l t (v : var l t) : F t ->  of_list l -> of_list l:=
      match v  with 
        | var_0 _ _ => fun x e => pair x (snd e)
        | var_S _ _ _ v => fun x e => pair (fst e) (set _ _ v x (snd e))
      end. 
    
    Definition init (el : forall t, F t) l : of_list l. 
    induction l. simpl. apply tt. 
    destruct l. simpl. auto. simpl. 
    split; auto. 
    Defined. 
  End t. 
  
  Section map2. 
    Context {T : Type} {F : T -> Type} {F' : T -> Type}. 
    Variable (up : forall a,  F a -> F' a -> F' a). 
    Definition map2 l : of_list T F l -> of_list T F' l -> of_list T F' l. 
    induction l. simpl. auto. 
    simpl. destruct l. apply up. intros [x xs] [y ys]. split; auto. 
    Defined. 
  End map2. 
End ETuple. 

Arguments ETuple.get {T F} l t _ _. 
Arguments ETuple.app {T F} l1 l2 _ _. 
Arguments ETuple.of_list {T} _ _ .  

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


Module Finite. 
  Record T ( n : nat) :Type := mk
    {
      val : nat;
      range : val < n
    }. 
  Arguments val {n} _. 

  Definition eqb {n} (x y : T n) :=
    NPeano.Nat.eqb (val x) (val y). 

  Definition ltb {n} (x y : T n) :=
    NPeano.Nat.ltb (val x) (val y). 
  Require NPeano. 
  Definition repr {n} (v : nat) : T (S n). 
  refine (mk (S n)  (NPeano.modulo v (S n)) _).
  abstract (apply NPeano.Nat.mod_upper_bound; discriminate). 
  Defined.
 
  Definition next {n} (x : T (S n)) :  T (S n) :=
    repr (S (val x)).  
                                
End Finite. 

Module Regfile2. 
    
  Record T (size : nat) (X : Type) := mk 
    {content : Vector.vector X size; 
     default : X}. 

  Arguments mk {size X} _ _. 
  Arguments content {size X} _. 

  Notation "! x" := (content x) (at level 70).
  
  Definition empty size X (el : X ): T size X := 
    mk (Vector.empty X size el) el. 
 
  (* Definition get {size X} (v : T size X) (n : nat) :=  *)
  (*   Vector.get _ _ (!v) n.  *)

  Definition get {size X} (v : T size X) (n : nat) : X :=
    match Vector.get _ _ (!v) n with 
      | Some x => x
      | None => default _ _ v
    end. 

  Definition set  {size X} (v : T size X) (addr : nat) (el : X) : T size X :=
    mk (Vector.set _ _ (!v) (addr)%nat el) (default _ _ v). 

  Definition of_list_pad {X} n (default : X) (l : list X) : T n X := 
    mk (Vector.of_list_pad _ n default l) default.  

End Regfile2. 

Module Regfile. 

  Record T (size : nat) (X : Type) : Type := mk
    {
      content : list X;
      hyp : List.length content = size
    }. 
  Arguments content {size X} t. 
  Arguments mk {size X} _ _. 
  Arguments hyp {size X} t. 
  Definition empty size {X} (el : X) : T size X.
  refine (  let l := (fix f n := match n with 0 => nil | S n => cons el (f n) end) size in  
              mk l _ ). 
  induction size. reflexivity. simpl in *. rewrite IHsize; reflexivity. 
  Defined. 
  
  Definition get {size X} (v : T size X) (n : Finite.T size) : X. 
  refine (let x := List.nth_error (content v)   (Finite.val n)  in _). 
  case_eq x; auto.
  destruct n as [n H]; destruct v as [l Hl]. simpl in *; subst x.    
  intros H'. exfalso. 
  revert H'. 
  admit. 
  Defined. 

  Fixpoint pt {A} (l : list A) n x :=
    match l with 
      | nil => nil
      | cons t q => match n with 
                       | 0 => cons x q
                       | S n => pt q n x
                   end
    end. 
  Definition set {size X} (v : T size X) (n : Finite.T size) (x : X) : (T size X). 
  destruct v as [l Hl]; destruct n as [n Hn].  
  apply (mk (pt l n x) ). 
  admit. 
  Defined. 
End Regfile. 
 
(* The base types, that exist in every language. These types should have:
   - decidable equality; 
   - default element (to initialize the arrays)
 *)
Inductive type0 : Type :=
| Tunit : type0 
| Tbool: type0 
| Tint: nat -> type0
| Tfin: nat -> type0
| Tabstract : ident -> Abstract.T -> type0. 

Fixpoint eval_type0 st : Type := 
  match st with 
    | Tunit => unit
    | Tbool => bool
    | Tint n => Word.T n
    | Tfin n => Finite.T n
    | Tabstract _ t => Abstract.carrier t
  end. 

Definition eval_type0_list l : Type := Tuple.of_list eval_type0 l. 

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
      | Tfin n => @Finite.eqb n
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
      | Tfin n => @Finite.ltb n
      | Tabstract _ t => Abstract.lt t
    end. 
End type_ops. 

 
Record signature T (E : T -> Type) := mk_signature
  {
    args : list T;
    res : T; 
    value :> Tuple.of_list E args -> E res
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
| BI_mux : forall t, builtin (B :: t :: t :: nil)%list t                         

(* integer operations *)
| BI_plus  : forall n, builtin (W n :: W n :: nil)%list (W n)
| BI_minus : forall n, builtin (W n :: W n :: nil)%list (W n)

| BI_next : forall n, builtin (Tfin (S n) :: nil) (Tfin (S n)). 


(* applies a ternary function to three arguments *)
Definition tri_op {a b c d } (f : eval_type0 a -> eval_type0 b -> eval_type0 c -> eval_type0 d) 
  : eval_type0_list (a :: b :: c :: nil)%list -> eval_type0 d :=
  fun X => match X with (x,(y,(z, tt))) => f x y z end. 

(* applies a binary function to two arguments *)
Definition bin_op {a b c} (f : eval_type0 a -> eval_type0 b -> eval_type0 c) 
  : eval_type0_list (a :: b :: nil)%list -> eval_type0 c :=
  fun X => match X with (x,(y,tt)) => f x y end. 

(* applies a unary function to one arguments *)
Definition un_op {a b} (f : eval_type0 a -> eval_type0 b) 
  : eval_type0_list (a :: nil) -> eval_type0 b :=
  fun X => match X with (x,tt) => f x end. 

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
    | BI_mux t => @tri_op B t t t (fun b x y => if b then x else y) 
    | BI_plus n => @bin_op (W n) (W n) (W n) (@Word.add n)
    | BI_minus n => @bin_op (W n) (W n) (W n) (@Word.minus n)
    | BI_next n => @un_op (Tfin (S n)) (Tfin (S n)) (@Finite.next n)
  end. 


Definition relation A := A -> A -> Prop. 
Definition union {A} (R S : relation A) := fun x y => R x y \/ S x y. 

Delimit Scope dlist_scope with dlist. 

Module DList. 
  Section t. 
  
  Variable X : Type. 
  Variable P : X -> Type. 
  Inductive T  : list X -> Type := 
      | nil : T nil
      | cons : forall (t : X) q, P t -> T q -> T (cons t q).  

  (** * Head and tail *)
  Arguments cons t q _ _%dlist. 
  Arguments T _%list. 
  Definition hd t q (x : T (t::q)): P t :=
    match x as y in T l return
       (match l return (T l -> Type) with 
         | [] => fun _ : T [] => ID
         | a::b => fun _ : T (a :: b) => P a
        end%list y)
    with 
      | nil => @id
      | cons _ _ t q => t
    end.

  Definition tl t q (x : T (t::q)): T q :=
    match x as y in T l return
       (match l return (T l -> Type) with 
         | [] => fun _ : T [] => ID
         | a::b => fun _ : T (a :: b) => T b
        end%list y)
    with 
      | nil => @id
      | cons _ _ t q => q
    end.

  (** * Concatenation of T (append)  *)
  Definition app : forall (l1 l2 : list X), 
                         T l1 -> T l2 -> T (List.app l1 l2).   
  refine (
      (fix app (l1 l2 : list X) {struct l1} :
       T l1 -> T l2 -> T (l1 ++ l2) :=
       match l1 as l3 return (T l3 -> T l2 -> T (l3 ++ l2)) with
         | [] => fun (_ : T []) (dl2 : T l2) => dl2
         | (t :: q)%list =>
             fun (dl1 : T (t :: q)) (dl2 : T l2) =>
               cons t (q ++ l2)%list (hd t q dl1)
                          (app q l2 (tl t q dl1) dl2)
      end%list)). 
  Defined. 
  

  (** * Other functions operating on tuples like things *)
  Variable E : X -> Type.
  
  Section foldo. 
    Variable F : forall (t : X), P t -> E t -> option (E t). 
    Fixpoint fold (l : list X) (d : T l) : Tuple.of_list E l -> option (Tuple.of_list E l):=
      match d with
          nil => fun v => Some v
        | cons t q pt dlq => fun v =>
            do x <- F t pt (fst v);
            do y <- fold q dlq (snd v);
            Some (x,y)
      end.
  End foldo. 

  Section s2. 
    Variable F : forall (t : X), P t -> E t. 

    Definition fold' (l : list X) (dl : T l) : Tuple.of_list E l. 
    induction dl. simpl. apply tt. 
    simpl. destruct q. auto. split. auto. auto. 
    Defined. 
  End s2. 

End t. 

Arguments T {X} P _%list. 
Arguments nil {X P}. 
Arguments cons {X P} {t q} _ _.  
(* Arguments fold' {X P E} _ _ _.  *)
Arguments app {X P l1 l2} _ _ . 

Definition to_tuple X (l : list X) F G  (Trans : forall x, F x -> G x): T F l -> Tuple.of_list G l. 
Proof. 
  induction 1. simpl. apply tt. 
  simpl. split. auto. auto. 
Defined. 

Arguments to_tuple {X l F G} Trans _%dlist. 

Definition to_etuple X (l : list X) F G  (Trans : forall x, F x -> G x): T F l -> ETuple.of_list G l. 
Proof. 
  induction 1. simpl. apply tt. 
  simpl. destruct q. auto. split.  auto. auto. 
Defined. 

Arguments to_etuple {X l F G} Trans _%dlist. 


  
Definition map  {X P Q} :
  forall (f : forall (x : X), P x -> Q x), 
  forall l, 
    @T X P l -> 
    @T X Q l. 
intros f. 
refine (fix F l (hl : T P l) : T Q l := 
        match hl with 
          | nil => nil
          | cons t q T Q => cons (f _ T) (F _ Q)
        end). 
Defined. 

Definition hmap :
  forall (X Y : Type) (P : Y -> Type) (Q : X -> Type)
    (F :  X -> Y), 
    (forall x : X, P (F x) -> Q x) -> forall l : list X, T P (List.map F l) -> T Q l. 
induction l. simpl. constructor. 
simpl. intros. inversion X1.   subst. constructor. auto. auto. 
Defined. 
 (*
Definition fold2 :
  forall (S T : Type) (P : T -> Type) (E : S -> Type)
    (F : S -> T),
    (forall t : S, P (F t) -> E t) -> forall l : list S, T P (List.map F l) -> Tuple.of_list E l. intros S T P E F f.
refine (let fix fold (l : list S) (dl : T P (List.map F l)) : Tuple.of_list E l :=
              match l return T P (List.map F l) -> Tuple.of_list E l with
                | nil =>  fun _ => tt
                | cons t q => fun x : T P (F t :: List.map F q) =>
                    (f  _ (hd _ _ _ _ x),  fold _ (tl _ _ _ _ x))
              end dl
          in fold).
Defined.
*)
Definition dmap {A B} (F : A -> Type) (G: B -> Type) (C : A -> B) (D : forall x, F x -> G ( C x)) (l: list  A) (dl : T F l) : T G (List.map C l). 
  induction dl. simpl. constructor. 
  simpl. constructor. apply D.  auto. 
  apply IHdl. 
Defined. 
End DList. 

Notation "[ ]" := DList.nil : dlist_scope.
Notation "t :: q" := (DList.cons t q) : dlist_scope.
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..)%dlist : dlist_scope.
