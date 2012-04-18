
(** Vectors: n-uples *)
Require List. 
Section t. 
  Variable t : Type. 
  Fixpoint vector n : Type := match n with 
                         | 0 => unit
                         | S n => (t * vector n)%type
                       end.

  Definition nil : vector 0 := tt. 
  Definition cons {n} x (v : vector n) : vector (S n) := 
    (x,v).

  Fixpoint get n : vector n -> nat ->  option t :=
    match n with 
      | 0 => fun _ _ => None
      | S n => fun v x => match x with 
                              | 0 => Some (fst v)
                              | S x => get n (snd v) x
                          end
    end.

  (* silently fails to update out of bounds values *)
  Fixpoint set n : vector n -> nat -> t -> vector n :=
    match n with 
      | 0 => fun v _ _ => v
      | S n => fun v x el => match x with 
                              | 0 => (el, snd v)
                              | S x => (fst v, set n (snd v) x el)
                          end
    end.

  Fixpoint empty n x : vector n :=
    match n with 
        | 0 => nil
        | S n => cons x (empty n x)
    end. 

  Fixpoint of_list (l : list t) : vector (List.length l) :=
    match l with 
      | List.nil => nil
      | List.cons t q => cons t (of_list q)
    end. 

  Fixpoint of_list_pad n (el : t) (l : list t) : vector n :=
    match n with 
        | 0 => nil
        | S p => match l with 
                  | List.nil => empty (S p) el
                  | List.cons t q => cons t (of_list_pad p el q)
                end
    end. 

End t. 

Section eq. 
  Context {A : Type} (eq : A -> A -> bool).
  Fixpoint veqb n  : vector A n -> vector A n -> bool :=
    match n with 
      0 => fun l l' => true
      | S n => fun l l' => 
        match l,l' with
          | (x,q), (x',q') => andb (eq x x') (veqb n q q')
        end
    end.
End eq. 

Arguments Scope vector [type_scope nat_scope]. 
Definition uncons {A} n (v : vector A (S n)) : A * vector A n := id v.
Lemma nil_eq {A} (u v : vector A 0) : u = v. 
Proof. 
  destruct u. destruct v. reflexivity. 
Qed.

Section map. 
  Context{ A B : Type} ( f : A -> B).
  Fixpoint map n : vector A n -> vector B n := match n with 
                      | 0 => fun _ => tt
                      | S p => fun v => 
                        match v with 
                          |(t,q) => (f t, map p q)
                        end
                    end.
End map. 
Section ops.
  Context {A B : Type}.

  Fixpoint vector_repeat n (x :A ) : vector A n :=
    match n with 
      | 0 => tt
      | S p => (x, vector_repeat p x)
    end. 
    
  Fixpoint last n x : vector A n -> A :=
    match n with 
      | 0 => fun _ => x 
      | S p => fun v => 
        match v with | (t,q) => last p t q end 
    end.
  
  Definition forget_right n (v : vector (A *B) n) : vector A n :=
  map (@fst A B) n v.

  Definition forget_left n (v : vector (A *B) n) : vector B n :=
    map (@snd A B) n v.

  Definition unzip n (v : vector (A *B) n) : vector A n * vector B n :=
     (forget_right n v , forget_left n v).
  
  Fixpoint zip n : 
    vector A n -> vector B n -> vector (A*B) n :=
    match n with 
      0 => fun _ _ => tt
      | S p => 
        fun v v' =>
          match v,v' with 
            | (t,q),(t',q') => ((t,t'), (zip p q q'))
          end
    end.
    
  Fixpoint append n m : vector A n ->  vector A m -> vector A (n +m) :=
  match n with 
    | 0 => fun u v => v
    | S p => 
      fun u v => 
        match u with 
          (t,q) => (t,append p m q v)
        end
  end.

  Fixpoint firstn  n m: vector A (n + m) -> vector A n :=
    match n with 
      | 0 => fun v => tt
      | S p => fun v => match v with 
                        | (t,q) => (t,firstn p m q)
                      end
    end.

  Fixpoint skipn  n m: vector A (n + m) -> vector A m :=
    match n with 
      | 0 => fun v => v
      | S p => fun v => match v with 
                        | (t,q) => (skipn p m q)
                      end
    end.

End ops. 

Section pointwise. 
  Context {A B : Type}.
  Context (R : A -> B -> Prop).
  
  Fixpoint pointwise n : vector A n -> vector B n -> Prop :=
    match n with 
      | 0 => fun _ _  => True
      | S p => fun u => fun v => 
        match u,v with 
          (t,q),(t',q') => R t t' /\ pointwise p q q'
        end
    end. 
End pointwise. 

Section pairmap.
  Context {A B : Type}.
  Variable f : A -> A -> B. 

  Fixpoint pairmap n x : vector A n -> vector B n :=
    match n with 
      | 0 => fun v => tt
      | S p => fun v => match v with 
                        | (t,q) => (f t x,pairmap p t q)
                      end
    end.
  Lemma pairmap_append x n m (s1 : vector A n) (s2 : vector A m) :
    pairmap (n + m) x (append n m s1 s2) = 
    append n m (pairmap n x s1) (pairmap m (last n x s1) s2).
  Proof. 
    revert x. 
    induction n; intros x.  simpl. reflexivity. 
    simpl in s1. destruct s1 as [t q].    
    simpl.
    rewrite IHn. 
    reflexivity. 
  Qed.
End pairmap. 

  

