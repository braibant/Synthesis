Require List. 
Require Import Common. 

Section dependent_lists. 
  
  Variable T : Type. 
  Variable P : T -> Type. 
  Inductive dlist  : list T -> Type := 
      | dlist_nil : dlist  nil
      | dlist_cons : forall (t : T) q, P t -> dlist q -> dlist (cons t q).  

  (** * Head and tail *)
  Definition dlist_hd t q (x : dlist (t::q)): P t :=
    match x as y in dlist l return
       (match l return (dlist l -> Type) with 
         | nil => fun _ : dlist nil => ID
         | cons a b => fun _ : dlist (cons a b) => P a
        end y)
    with 
      | dlist_nil => @id
      | dlist_cons _ _ t q => t
    end.

  Definition dlist_tl t q (x : dlist (t::q)): dlist q :=
    match x as y in dlist l return
       (match l return (dlist l -> Type) with 
         | nil => fun _ : dlist nil => ID
         | cons a b => fun _ : dlist (cons a b) => dlist b
        end y)
    with 
      | dlist_nil => @id
      | dlist_cons _ _ t q => q
    end.

  (** * Concatenation of dlist (append)  *)
  Definition dlist_app : forall (l1 l2 : list T), 
                         dlist l1 -> dlist l2 -> dlist (List.app l1 l2).   
  refine (
      (fix dlist_app (l1 l2 : list T) {struct l1} :
       dlist l1 -> dlist l2 -> dlist (l1 ++ l2) :=
       match l1 as l3 return (dlist l3 -> dlist l2 -> dlist (l3 ++ l2)) with
         | nil => fun (_ : dlist []) (dl2 : dlist l2) => dl2
         | (t :: q)%list =>
             fun (dl1 : dlist (t :: q)) (dl2 : dlist l2) =>
               dlist_cons t (q ++ l2) (dlist_hd t q dl1)
                          (dlist_app q l2 (dlist_tl t q dl1) dl2)
      end)). 
  Defined. 
  

  (** * Other functions operating on tuples like things *)
  Variable E : T -> Type.
  
  Section foldo. 
    Variable F : forall (t : T), P t -> E t -> option (E t). 
    Fixpoint dlist_fold (l : list T) (d : dlist l) : Tuple.of_list E l -> option (Tuple.of_list E l):=
      match d with
          dlist_nil => fun v => Some v
        | dlist_cons t q pt dlq => fun v =>
            do x <- F t pt (fst v);
            do y <- dlist_fold q dlq (snd v);
            Some (x,y)
      end.
  End foldo. 

  Section s2. 
    Variable F : forall (t : T), P t -> E t. 

    Definition dlist_fold' (l : list T) (dl : dlist l) : Tuple.of_list E l. 
    induction dl. simpl. apply tt. 
    simpl. destruct q. auto. split. auto. auto. 
    Defined. 
  End s2. 

End dependent_lists. 

Arguments dlist {T} P _. 
Arguments dlist_nil {T P}. 
Arguments dlist_cons {T P} {t q} _ _.  
(* Arguments dlist_fold' {T P E} _ _ _.  *)
Arguments dlist_app {T P l1 l2} _ _ . 

Definition to_tuple T (l : list T) F G  (Trans : forall x, F x -> G x): dlist F l -> Tuple.of_list G l. 
Proof. 
  induction 1. simpl. apply tt. 
  simpl. split. auto. auto. 
Defined. 

Arguments to_tuple {T l F G} Trans _%dlist. 

Definition to_etuple T (l : list T) F G  (Trans : forall x, F x -> G x): dlist F l -> ETuple.of_list G l. 
Proof. 
  induction 1. simpl. apply tt. 
  simpl. destruct q. auto. split.  auto. auto. 
Defined. 

Arguments to_etuple {T l F G} Trans _%dlist. 


  
Definition dlist_map  {T P Q} :
  forall (f : forall (x : T), P x -> Q x), 
  forall l, 
    @dlist T P l -> 
    @dlist T Q l. 
intros f. 
refine (fix F l (hl : dlist P l) : dlist Q l := 
        match hl with 
          | dlist_nil => dlist_nil
          | dlist_cons t q T Q => dlist_cons (f _ T) (F _ Q)
        end). 
Defined. 

Definition dlist_hmap :
  forall (S T : Type) (P : T -> Type) (Q : S -> Type)
    (F : S -> T), 
    (forall x : S, P (F x) -> Q x) -> forall l : list S, dlist P (List.map F l) -> dlist Q l. 
induction l. simpl. constructor. 
simpl. intros. inversion X0.   subst. constructor. auto. auto. 
Defined. 

Definition dlist_fold2 :
  forall (S T : Type) (P : T -> Type) (E : S -> Type)
    (F : S -> T),
    (forall t : S, P (F t) -> E t) -> forall l : list S, dlist P (List.map F l) -> Tuple.of_list E l. intros S T P E F f.
refine (let fix fold (l : list S) (dl : dlist P (List.map F l)) : Tuple.of_list E l :=
              match l return dlist P (List.map F l) -> Tuple.of_list E l with
                | nil =>  fun _ => tt
                | cons t q => fun x : dlist P (F t :: List.map F q) =>
                    (f  _ (dlist_hd _ _ _ _ x),  fold _ (dlist_tl _ _ _ _ x))
              end dl
          in fold).
Defined.

Definition dmap {A B} (F : A -> Type) (G: B -> Type) (C : A -> B) (D : forall x, F x -> G ( C x)) (l: list  A) (dl : DList.dlist F l) : DList.dlist G (List.map C l). 
  induction dl. simpl. constructor. 
  simpl. constructor. apply D.  auto. 
  apply IHdl. 
Defined. 

