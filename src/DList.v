
Require List Common. 

Import Common. 

Open Scope list_scope. 

Notation "[ ]" := nil : list_scope.
Notation "t :: q" := (cons t q) : list_scope. 
Notation "[ a ; .. ; b ]" := (a :: .. (b :: []) ..)%list : list_scope.

Module DList. 
Section t. 
  
  Variable X : Type. 
  Variable P : X -> Type. 
 
  Inductive T  : list X -> Type := 
  | nil : T nil
  | cons : forall (t : X) q, P t -> T q -> T (cons t q).  
  
  Arguments cons t q%list _ _%dlist. 
  Arguments T _%list. 

  Definition hd t q (x : T (t::q)): P t :=
    match x as y in T l return
       (match l return (T l -> Type) with 
         | [ ] => fun _ : T [] => ID
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


  Fixpoint get l t (v: var l t): T l -> P t :=
    match v with 
      | var_0  _ _ => fun e => hd _ _ e
      | var_S _ _ _ v => fun e => get _ _ v  (tl _ _ e)
      end. 

  Fixpoint set l t (v : var l t) : P t ->  T l -> T l:=
    match v  with 
        | var_0 _ _ => fun x e => cons _ _  x (tl _ _ e)
        | var_S _ _ _ v => fun x e => cons _ _  (hd _ _ e) (set _ _ v x (tl _ _ e))
    end. 

  (** * Operations  *)
  Fixpoint Forall (Q: forall (x : X), P x -> Prop) l (dl : T l) :=
    match dl with 
      | nil => True
      | cons t q dt dq => Q t dt /\ Forall Q q dq
    end. 
  
  Fixpoint init (el : forall t, P t) l : T l :=
    match l with 
      | List.nil => nil
      | List.cons t q => cons _ _ (el t) (init el q)
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
  

  (* (** * Other functions operating on tuples like things *) *)
  (* Variable E : X -> Type. *)
  
  (* Section foldo.  *)
  (*   Variable F : forall (t : X), P t -> E t -> option (E t).  *)
  (*   Fixpoint fold (l : list X) (d : T l) : Tuple.of_list E l -> option (Tuple.of_list E l):= *)
  (*     match d with *)
  (*         nil => fun v => Some v *)
  (*       | cons t q pt dlq => fun v => *)
  (*           do x <- F t pt (fst v); *)
  (*           do y <- fold q dlq (snd v); *)
  (*           Some (x,y) *)
  (*     end. *)
  (* End foldo.  *)

  (* Section s2.  *)

  (*   Variable F : forall (t : X), P t -> E t.  *)

  (*   Definition fold' (l : list X) (dl : T l) : Tuple.of_list E l.  *)
  (*   induction dl. simpl. apply tt.  *)
  (*   simpl. destruct q. auto. split. auto. auto.  *)
  (*   Defined.  *)
  (* End s2.  *)

End t. 

Arguments T {X} P _%list. 
Arguments nil {X P}. 
Arguments cons {X P} {t q} _ _%dlist.  

Arguments app {X P l1 l2} _%dlist _%dlist. 
Arguments get {X P l t} _ _%dlist.  
Arguments set {X P l t} _ _ _%dlist.  

Arguments Forall {X P} _ {l}%list _%dlist. 
Arguments init {X P} _ l%list.

Section ops. 
  Variable X : Type. 
  Variable (F G : X -> Type). 
  Variable (Op : forall x, F x -> G x). 
  Definition to_tuple (l : list X) : T F l -> Tuple.of_list G l. 
  refine ((fix F l (hl : T F l) : Tuple.of_list G l :=
           match hl in T _ l return Tuple.of_list G l with 
                                  | nil => tt
                                  | cons t q T Q =>  ((Op t T),(F q Q))
           end) l).
  Defined. 

  
  Definition map ( l : list X) : T F l -> T G l. 
  refine ((fix F l (hl : T F l) : T G l := 
          match hl in T _ l return T G l with 
            | nil => nil
            | cons t q T Q => cons (Op _ T) (F _ Q)
          end) l). 
  Defined. 
End ops. 
Arguments to_tuple {X F G} Op {_} _%dlist. 
Arguments map {X F G} Op {_} _%dlist. 

Lemma map_to_tuple_commute {X} (F G H : X -> Type)
                            (Op : forall x, F x -> G x) (Op' : forall x : X, G x -> H x)
                            (l : list X) (dl : T F l) :
  to_tuple Op' (map Op dl) = 
  to_tuple (fun x dx => Op' x (Op x dx)) dl. 
Proof.
  induction dl. reflexivity.
  simpl. f_equal. apply IHdl. 
Qed. 
  
Definition hmap :
  forall (X Y : Type) (P : Y -> Type) (Q : X -> Type)
    (F :  X -> Y), 
    (forall x : X, P (F x) -> Q x) -> forall l : list X, T P (List.map F l) -> T Q l. 
induction l. simpl. constructor. 
simpl. intros. inversion X1.   subst. constructor. auto. auto. 
Defined. 

Definition dmap {A B} (F : A -> Type) (G: B -> Type) (C : A -> B) (D : forall x, F x -> G ( C x)) (l: list  A) (dl : T F l) : T G (List.map C l). 
  induction dl. simpl. constructor. 
  simpl. constructor. apply D.  auto. 
  apply IHdl. 
Defined. 

Inductive pointwise {A} F G (R : forall a, F a -> G a -> Type): forall (l : list A), T F l -> T G l -> Type :=
| pointwise_nil : pointwise F G R List.nil nil nil
| pointwise_cons : forall t q dt1 dt2 dq1 dq2,
                     R t dt1 dt2 -> 
                     pointwise F G R q dq1 dq2 ->
                     pointwise F G R (t::q) (cons dt1 dq1) (cons dt2 dq2). 
Arguments hd {X P t q} _%dlist.  
Arguments tl {X P t q} _%dlist.  
Section map3. 
  Context {X : Type} {F F' F'': X -> Type}.
  Variable (up : forall a,  F a -> F' a -> F'' a -> F'' a). 
  Fixpoint map3 l : T F l -> T F' l -> T F'' l -> T F'' l :=
    match l with 
      | List.nil => fun _ _ x => x
      | List.cons t q => fun xs ys zs => 
                         let (x,xs) := (hd xs, tl xs) in 
                         let (y,ys) := (hd ys, tl ys) in 
                         let (z,zs) := (hd zs, tl zs) in 
                           cons (up t x y z)  (map3 q xs ys zs)
    end. 
End map3. 

Section map3o. 
  Context {X : Type} {F F' F'': X -> Type}.
  Variable (up : forall a,  F a -> F' a -> F'' a -> option (F'' a)). 
  Fixpoint map3o l :  T F l ->  T F' l ->  T F'' l -> option (T F'' l) :=
    match l with 
        | List.nil => fun _ _ x => Some x
        | List.cons t q => fun xs ys zs => 
                         let (x,xs) := (hd xs, tl xs) in 
                         let (y,ys) := (hd ys, tl ys) in 
                         let (z,zs) := (hd zs, tl zs) in 
                           do t <- up t x y z;
                           do q <- map3o q xs ys zs;
                           Some (cons t q) 
    end. 
End map3o. 

Theorem map3_map : forall (X : Type) (F F' F'' : X -> Type)
  (f : forall a : X, F a -> F' a -> F'' a -> F'' a)
  l (dl1 dl1' : T F l),
  pointwise _ _ (fun a (x1 x1' : F a) => forall x2 x3, f a x1 x2 x3 = f a x1' x2 x3) _ dl1 dl1'
  -> forall (dl2 : T F' l) (dl3 : T F'' l),
    map3 f l dl1 dl2 dl3 = map3 f l dl1' dl2 dl3.
Proof. 
  induction 1; simpl; intuition.
  f_equal; auto.
Qed.

Lemma pointwise_map : forall (A : Type) (F G G' : A -> Type)
  (P : forall a : A, F a -> G a -> Type)
  (Q : forall a : A, F a -> G' a -> Type)
  (f : forall a : A, G a -> G' a)
  (_ : forall t dt1 dt2, P t dt1 dt2 -> Q t dt1 (f t dt2))
  l (dl1 : T F l) (dl2 : T G l),
  pointwise _ _ P _ dl1 dl2
  -> pointwise _ _ Q _ dl1 (map f dl2).
Proof. 
  induction 2; simpl; intuition; constructor; intuition. 
Qed.

Require Import Equality.

Lemma inversion_dlist_cons {A F} : forall (t : A) q (dl : T F (t :: q)), 
                              {hd : F t & {tl : T F q | dl = (cons hd tl)%dlist}}. 
Proof. 
  intros.  dependent destruction dl. eauto. 
Qed. 

Lemma inversion_dlist_nil {A} {F : A -> Type}  (dl : T F []) :
                              dl = (nil)%dlist. 
Proof. 
  dependent destruction dl. reflexivity. 
Qed. 

Require Import Equality.
Lemma inversion_pointwise {A F G} P (t : A) q dt dq dt' dq':
  pointwise F G P (t :: q)%list (cons dt dq) (cons dt'  dq') ->
  pointwise F G P q dq dq' * P t dt dt'. 
Proof. 
  intros H.  
  inversion H;
    repeat match goal with 
               H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H
           end; subst; auto. 
Qed. 

Ltac inversion :=
  match goal with 
    | H : DList.T _ (_ :: _) |- _ => 
        destruct (inversion_dlist_cons _ _ H) as [? [? ?]]
    | H : DList.T _ ([]) |- _ => 
        pose proof (inversion_dlist_nil H)
  end; subst. 


Arguments DList.pointwise {A F G} _ l%list _%dlist _%dlist. 

Ltac inv :=
  repeat 
    match goal with 
      | H : DList.T _ (_ :: _) |- _ => 
        destruct (inversion_dlist_cons _ _ H) as [? [? ?]]; subst        
      | H : DList.T _ ([]) |- _ => 
        pose proof (inversion_dlist_nil H); subst
      | H : pointwise _ ( _ :: _ ) (cons _ _) (cons _ _) |- _ => 
        apply inversion_pointwise in H; 
        destruct H as [? ?]                                                              
    end. 

(** * [existb f dl] tests whether an element of [dl] satisfies the predicate [f] *)
Section existb. 
  Variable (X: Type) (F: X -> Type).
  Variable (f: forall (x: X) (dx: F x), bool). 
  Fixpoint existb (l: list X) (dl: T F l) : bool :=
    match dl with 
      | DList.nil => false
      | DList.cons t q dt dq => (f t dt || existb q dq)%bool
    end.
End existb. 
Arguments existb {X F} _ {l} dl%dlist. 

(** [mapo f dl] applies the partial function [f] to every element of
[dl]. If any such application fails (i.e., returns [None]), then [mapo
f dl] fails.  *)

Section mapo.
  Variable (X : Type). Variable F G: X -> Type. 
  Variable f: forall (x:X) (dx: F x), option (G x). 
  
  Fixpoint mapo (l:list X) (dl: DList.T F l) : option (DList.T G l) :=
    match dl with 
      | DList.nil => Some (DList.nil)
      | DList.cons t q dt dq => 
          do dt <- f t dt;
          do dq <- mapo q dq;
          Some (cons dt dq)
    end%dlist. 
End mapo. 
Arguments mapo {X F G} _ {l} dl%dlist. 

(** [fold f dl acc] fold the function [f] through [dl], starting with
the accumulator [acc]. The type of the accumulator is static. *)

Section fold.
  Variable X A: Type. Variable F : X -> Type. 
  Variable f: forall (x:X) (dx: F x), A -> A. 
  
  Fixpoint fold (l:list X) (dl: DList.T F l) acc: A :=
    match dl with 
      | DList.nil => acc
      | DList.cons t q dt dq => 
          f t dt (fold q dq acc)
    end%dlist. 
End fold. 

Arguments fold {X A F} f {l} dl%dlist acc. 

    
End DList. 

Notation "[ :: ]" := DList.nil : dlist_scope.
Notation "t :: q" := (DList.cons t q) : dlist_scope.
Notation "[ :: a ; .. ; b ]" := (a :: .. (b :: [ :: ]) ..)%dlist : dlist_scope.

