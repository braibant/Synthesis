Require Export String. 
(* Require Vector.  *)

Definition bind {A B: Type} (f: option A) (g: A -> option B) : option B :=
  match f with
    | Some x => g x
    | None => None
  end.

Definition bind2 {A B C: Type} (f: option (A * B)) (g: A -> B -> option C) : option C :=
  match f with
  | Some (x, y) => g x y
  | None => None
  end.

Remark bind_inversion:
  forall (A B: Type) (f: option A) (g: A -> option B) (y: B),
  bind f g = Some y ->
  {x | f = Some x /\ g x = Some y}.
Proof. 
  intros; destruct f.  simpl in H.
  exists a; auto. 
  discriminate. 
Qed. 

Remark bind_inversion_None {A B} x (f: A -> option B) : bind x f = None -> 
  (x = None) + (exists y, x = Some y /\ f y = None).
Proof. 
  destruct x; simpl; intuition.
  right. exists a; intuition.  
Qed. 

Remark bind2_inversion:
  forall {A B C: Type} (f: option (A*B)) (g: A -> B -> option C) (y: C),
    bind2 f g = Some y ->
      {x1 : A & {x2 : B | f = Some (x1,x2) /\ g x1 x2 = Some y}}.
Proof. 
  intros ? ? ? [ [x y] | ] ? ? H; simpl in H; eauto.
  discriminate. 
Qed.

Notation "'do' X <- A ; B" := (bind A (fun X => B) )
  (at level 200, X ident, A at level 100, B at level 200). 

Notation "'do' X , Y  <- A ; B" := (bind2 A (fun X Y => B))
 (at level 200, X ident, Y ident, A at level 100, B at level 200).


Notation "'check' A ; B" := (if A then B else None)
  (at level 200, A at level 100, B at level 200). 

Ltac invert_do H :=
  match type of H with
    | (Some _ = Some _) =>
        inversion H; clear H; try subst
    | (None = Some _) =>
        discriminate
    | (bind ?F ?G = Some ?X) => 
        let x := fresh "x" in
          let EQ1 := fresh "EQ" in
            let EQ2 := fresh "EQ" in
              destruct (bind_inversion _ _ F G _ H) as [x [EQ1 EQ2]];
        clear H;
        try (invert_do EQ2)
    | (bind ?x ?f = None) => 
        let EQ := fresh "EQ" in 
        let EQ1 := fresh "EQ" in
        let EQ2 := fresh "EQ" in
        let x' := fresh "x" in 
        destruct (bind_inversion_None x f H) as [EQ | [x' [EQ1 EQ2]]];
        clear H;
        try (invert_do EQ1);
        try (invert_do EQ2);
        try (invert_do EQ)
  end. 
  
Definition admit {X : Type} : X.  Admitted.

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

  Fixpoint var_eqb {l t t'} (v : var l t) (v' : var l t') : bool :=
    match v in var l t return var l t' -> bool with 
      | var_0 _ _ => 
          fun v' => match v' with 
                     | var_0 _ _ => true 
                     | var_S _ _ _ _ => false
                   end
      | var_S E hd t v => 
          fun v' => 
            (match v' in var L T return
                match L with 
                  | nil => ID
                  | hd :: E => var E t -> bool
                end%list
             with
               | var_0 _ _ => fun _ => false
               | var_S _ _ _ v' => fun v => var_eqb v v'
             end v)
    end v'. 
  Lemma var_eqb_correct_1 l t t' (v: var l t ) (v': var l t') : 
    var_eqb v v' = true ->  t = t'.
  Proof. 
    Require Import Equality. 
    revert v'. induction v;  dependent destruction v'; simpl; intuition.  
    apply IHv in H. auto. 
  Qed. 
  Lemma var_eqb_correct_2 l t (v: var l t ) (v': var l t) : 
    var_eqb v v' = true ->  v = v'. 
  Proof. 
    revert v'.  induction v;  dependent destruction v'; simpl; intuition.  
    apply IHv in H. subst.  congruence. 
  Qed. 

End var. 

Arguments var {T} _ _. 
Arguments var_0 {T} {E} {t}. 
Arguments var_S {T} {E} {t} {t'} _. 
Arguments var_lift {T E F t} v. 
Arguments var_eqb {T l t t'} _ _. 

Fixpoint var_map {A B: Type} (F : A -> B) (l : list A) t (v : var l t) : var (List.map F l) (F t) :=
  match v with
    | var_0 E t => var_0 
    | var_S E t t' x => var_S (var_map F E _ x)
  end. 


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

  Section map. 
    Context {T : Type} {F F': T -> Type}.
    Variable (up : forall a,  F a -> F' a ).
    Fixpoint map l : of_list T F l -> of_list T F' l :=
      match l with 
        | nil => fun x => x
        | cons t q => fun xs =>
                       let (x,xs) := xs in 
                         (up t x, map q xs)
      end. 
  End map. 

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
    Fixpoint map3 l : of_list T F l -> of_list T F' l -> of_list T F'' l -> of_list T F'' l :=
      match l with 
        | nil => fun _ _ x => x
        | cons t q => fun xs ys zs => 
                       let (x,xs) := xs in 
                        let (y,ys) := ys in 
                          let (z,zs) := zs in 
                            (up t x y z, map3 q xs ys zs)
      end. 
  End map3. 

  Section map3o. 
    Context {T : Type} {F F' F'': T -> Type}.
    Variable (up : forall a,  F a -> F' a -> F'' a -> option (F'' a)). 
    Fixpoint map3o l : of_list T F l -> of_list T F' l -> of_list T F'' l -> option (of_list T F'' l) :=
      match l with 
        | nil => fun _ _ x => Some x
        | cons t q => fun xs ys zs => 
                       let (x,xs) := xs in 
                       let (y,ys) := ys in 
                       let (z,zs) := zs in 
                         do t <- up t x y z;
                         do q <- map3o q xs ys zs;
                         Some (t,q) 
      end. 
  End map3o. 
  
  Section fold. 
    Context {T B : Type} {F : T -> Type}. 
    Section inner. 
      Variable l : list T. 
      Variable up : forall a, F a -> var l a -> B -> B.
      
      Fixpoint prefold   s :
        (forall x, var s x -> var l x) -> of_list T F s -> B -> B :=
        match s as s' return  (forall x, var s' x -> var l x) -> of_list T F s' -> B -> B with
          | nil => fun  _ _ acc => acc
          | cons t q => fun f  (X : F t * of_list T F q) acc => 
                     let (x,xs) := X in 
                       let f' := fun x v => f x (var_S v) in
                         (up t x (f t var_0) (prefold q f' xs  acc))
                              
        end.  
      Definition fold   : of_list T F l -> B -> B := (prefold  l (fun x v => v)). 

    End inner. 
    Notation lift f := (fun x v => f x (var_S v)). 
  End fold. 
  Definition fst {T F l} {t: T} : (Tuple.of_list _ F (t::l)%list) -> F t. apply fst. Defined. 
  Definition snd {T F l} {t: T} : (Tuple.of_list _ F (t::l)%list) -> Tuple.of_list _ F l. apply snd. Defined. 

  Inductive pointwise {A} F G (R : forall a, F a -> G a -> Prop): forall (l : list A), Tuple.of_list _ F l -> Tuple.of_list _ G l -> Prop :=
  | pointwise_nil : pointwise F G R List.nil tt tt
  | pointwise_cons : forall t q dt1 dt2 dq1 dq2,
                       R t dt1 dt2 -> 
                       pointwise F G R q dq1 dq2 ->
                       pointwise F G R (t::q) (dt1,dq1) (dt2,dq2). 
  

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
Require Array. 
Module Regfile := Array. 

(*

(* Notation "<: val 'as' 'int' n :>" := (Word.mk n val _).  *)

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

*)
 

Definition relation A := A -> A -> Prop. 
Definition union {A} (R S : relation A) := fun x y => R x y \/ S x y. 

Delimit Scope dlist_scope with dlist. 

