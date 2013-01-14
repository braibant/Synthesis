Require Import Common Core Front ZArith Structures. 


Section t. 
  Variable A : Type. 
  
  (** Sequences of length [2^n] are defined as complete binary trees, with data on the leaves *)

  Inductive tree : nat -> Type :=
  | L : forall x : A, tree 0
  | N : forall n (l r : tree n), tree (S n). 

  (** Destructors for the [tree] data-type  *)

  Definition leaf (l : tree 0) : A := match l with 
                                        | L x => x
                                      end. 
  
  Definition left {n} (l : tree (S n)) : tree n := 
    match l with 
      | N _ l _ => l
    end. 
  Definition right {n} (l : tree (S n)) : tree n := 
    match l with 
      | N _ _ r => r
    end. 

  (**   *)
  Fixpoint Forall {n} (t : tree n) f :=
    match t with 
      | L x => f x
      | N _ l r => (Forall l f && Forall r f)%bool
    end.  
End t. 


(* Setting up implicit arguments *)
Arguments L {A} x. Arguments N {A} n l r.
Arguments leaf {A} l. Arguments left {A n} l. Arguments right {A n} l.
Arguments Forall {A n} _ _.  

(** Map operation on trees  *)
Fixpoint map {A B n} (f :A -> B) : tree A n -> tree B n :=
  match n with 
    | 0 => fun t => let x := leaf t in L (f x)
    | S n => fun t => N _ (map f (left t)) (map f (right t))
  end. 

Module Spec. 
  
  (** This modules define the specification of our sorting network: we
  implement the underlying sorting algorithm, and prove that it sorts
  its input sequence*)
  
  Section t. 
    Variable A : Type. 
    
    Fixpoint reverse n (t : tree A n) :=
      match t with 
        | L x => L x
        | N n l r => N n
                      (reverse n r)
                      (reverse n l)
      end.
    
    Variable (O : order A).
    Fixpoint min_max_swap n : forall (l r : tree A n), tree A n * tree A n :=
      match n return tree A n -> tree A n -> tree A n * tree A n with 
        | 0 => fun l r => let (x,y) := cmp (leaf l) (leaf r) in (L x, L y)
        | S n => fun l r => 
                  let (a,b) := min_max_swap _ (left l) (left r) in 
                  let (c,d) := min_max_swap _ (right l) (right r)in 
                  (N _ a c, N _ b d)
      end. 
    
    Fixpoint merge n: tree A n -> tree A n := 
      match n with 
        | 0 => fun t => t
        | S k => fun t => let (a,b) := min_max_swap _ (left t) (right t) in
                        N _ (merge _ a) (merge _ b)
      end. 
    
    Fixpoint sort n : tree A n -> tree A n :=
      match n with 
        | 0 => fun t => t
        | S n => fun t => 
                  let l := left t in 
                  let r := right t in 
                  merge (S n) (N _ (sort _ l) (reverse _ (sort _ r)))
    end. 
    
    Fixpoint list_of_tree {n} (t : tree A n) :=
      match t with 
        | L x => cons x nil
        | N _ l r => List.app (list_of_tree l) (list_of_tree r)
      end. 
    
    Fixpoint tree_of_list n (l: list A) : option (tree A n * list A) := 
      match n with 
        | 0 => match l with 
                | nil => None
                | cons t q => Some (L t, q)
            end
        | S n => do l, tl <- tree_of_list n l;
                do r, tl <- tree_of_list n tl;
                Some (N _ l r, tl)
      end. 
  End t.
  
  Module SameElements. 
    Section t. 
      Variable A : Type.
      Variable O : order A. 
    Require Import Permutation. 
    Require Import Setoid.   
    
    Definition equiv {n} (t1 : tree A n) (t2: tree A n) := Permutation (list_of_tree _ t1) (list_of_tree _ t2).
    
    Notation "t1 ~~ t2" := (equiv t1 t2) (at level 67). 
    Notation sort t := (sort A O _ t).
    
    Instance equiv_refl {n}: Reflexive (@equiv n).  Proof. repeat intro. apply Permutation_refl. Qed.
    Instance equiv_sym {n} : Symmetric (@equiv n). Proof. repeat intro. apply Permutation_sym;auto. Qed.
    Instance equiv_trans {n} : Transitive (@equiv n). Proof. repeat intro;eapply Permutation_trans;eauto. Qed.

    Lemma N_morphism n t1 t2 t1' t2' : t1 ~~ t1' -> t2 ~~ t2' -> N n t1 t2 ~~ N n t1' t2'.
    Proof. 
      unfold equiv. simpl. apply Permutation_app. 
    Qed. 

    Lemma N_morphism_swap n t1 t2 t1' t2' : t1 ~~ t2' -> t2 ~~ t1' -> N n t1 t2 ~~ N n t1' t2'.
    Proof. 
      unfold equiv. simpl. intros. rewrite Permutation_app_comm.  apply Permutation_app; auto. 
    Qed. 
    Require Import Equality. 
    Notation "x == y" := (Permutation x y) (at level 70).
    Require Import Morphisms. 

    Instance app_proper A : Proper (@Permutation A ==> @Permutation A ==> @Permutation A)(@List.app  A).
    Proof. 
      repeat intro. apply Permutation_app. auto. auto. 
    Qed. 

    Instance N_proper n : Proper (@equiv n ==> @equiv n ==> @equiv (S n))(N n).
    Proof. 
      repeat intro. apply N_morphism; auto. 
    Qed. 

    Lemma min_max_swap_equiv n: forall t1 t2  a b,          min_max_swap A O n t1 t2 = (a,b) -> 
                                                       N n a b ~~ N n t1 t2. 
    Proof. 
      induction n; dependent destruction t1; dependent destruction t2; 
      dependent destruction a; dependent destruction b; simpl. 
      + intros H; inject H. unfold equiv. simpl. 
        unfold min, max. destruct (x <= x0) eqn:H. auto.
        apply perm_swap; auto. 
      + intros.
        destruct (min_max_swap A O n t1_1 t2_1) eqn:H1.             
        destruct (min_max_swap A O n t1_2 t2_2) eqn:H2.             
        apply IHn in H1. apply IHn in H2. 
        inject H; injectT. clear IHn. 
        unfold equiv in *. simpl in *.          revert H1 H2. 
        repeat match goal with |- context [list_of_tree A ?x] => generalize (list_of_tree A x); intro end. 
        intros. 
        assert (H := Permutation_app H1 H2). clear H1 H2. 
        repeat rewrite  List.app_assoc in *.             
        clear - H. 

        rewrite <- (List.app_assoc l l3 l0). 
        rewrite (Permutation_app_comm l3 l0). 
        rewrite  (List.app_assoc l l0 l3).  rewrite H.
        apply Permutation_app; auto. 
        rewrite <- (List.app_assoc l1 l2 l5). 
        rewrite (Permutation_app_comm l2 l5). 
        rewrite  (List.app_assoc l1 l5 l2).  
        auto. 
    Qed.
        
    Lemma reverse_equiv {n} t: reverse A n  t ~~ t. 
    Proof. 
      induction n; simpl; dependent destruction t; simpl. 
      + reflexivity.   
      + apply N_morphism_swap. auto. auto.
    Qed. 

    Lemma merge_equiv : forall n t, merge A O n t ~~ t.  
    Proof. 
      induction n; simpl; dependent destruction t.
      + reflexivity. 
      + simpl. destruct (min_max_swap A O n t1 t2) as [a b] eqn:Hab.  apply min_max_swap_equiv in Hab. 
        rewrite IHn. rewrite IHn. auto. 
    Qed.

    Hint Resolve merge_equiv reverse_equiv min_max_swap_equiv. 
    
    Theorem sort_equiv : forall n (t: tree A n), sort t ~~ t.   
    Proof. 
      induction n; simpl; dependent destruction t; simpl.
      + reflexivity. 
      + destruct (min_max_swap A O n (sort t1) (reverse A n (sort t2))) as [a b] eqn:H. 
        transitivity (N n a b). 
        apply N_morphism; auto.  
        apply min_max_swap_equiv in H. 
        rewrite H.  apply N_morphism. auto.     
        rewrite reverse_equiv. auto. 
    Qed.
  End t.
  End SameElements. 
    

      
  
  Notation "t /<= a" := (Forall  t (fun x => x <= a)) (at level 79, left associativity).
  
  (** [l /<=\ r] means that all elements in [l] are smaller than the elements in [r] *)
  Notation "l /<=\ r" := (Forall  r (fun a => (Forall l (fun x => x <= a)))) (at level 50).

  (** [[:: l <= r]] means that all elements in the list [l] are smaller than the elements in [r]  *)

  Notation "[:: l <= r ]" := (List.Forall (fun x => List.Forall (fun y => y <= x = true) l) r) (r, l at next level).
  
  (** [tsorted n t] holds if the tree [t] is sorted with respect to the implicit order *)
  Inductive tsorted {A} {O : order A} : forall n, tree A n -> Prop :=
  | tsorted_L : forall x, tsorted 0 (L  x)
  | tsorted_N : forall n l r, tsorted n l -> tsorted n r -> 
                         l /<=\ r = true -> tsorted _ (N  _ l r).
  
  (** These labeles describe the various bitonic sequences cases *)
  Inductive bitonic_label : Type :=
  | O | I | OI | IO | OIO | IOI | W.
  
  (** Appending bitonic sequences with labels [l1] and [l2] yields a
 sequence whose label is [compose l1 l2] *)

  Definition compose l1 l2 :=
    match l1,l2 with 
      (* O *)
      | O, O => O
      (* OI *)
      | I, I => I
      (* OI *)
      | O, I => OI 
      | O, OI => OI
      | OI, I => OI
      (* IO *)
      | I, O => IO
      | I, IO => IO
      | IO, O => IO 
      (* OIO *)
      | O, IO 
      | OI, O
      | O, OIO 
      | OIO, O 
      | OI, IO => OIO
      (* IOI *)
      | I, IOI 
      | IOI, I 
      | I, OI 
      | IO, I 
      | IO, OI => IOI
      (* W *)
      | _, _ => W
    end. 
  
  (** [label t]  computes the label associated with the sequence [t] *)
  Fixpoint label {n} (t : tree bool n) := 
    match t with
      | L x => if x then I else O
      | N  _ l r => compose (label l) (label r) 
    end. 
  
  
  Lemma label_O_x_leq : forall n (t1: tree bool n) m (t2 : tree bool m), label t1 = O -> t1 /<=\ t2 = true. 
  Proof. 
    induction t1. 
    + simpl. destruct x. discriminate. 
      intros  m t2 _. induction t2. trivial. simpl in * . rewrite IHt2_1. rewrite IHt2_2.  reflexivity.
    + simpl. 
      destruct (label t1_1) eqn: H1; try discriminate;
      destruct (label t1_2) eqn: H2; try discriminate. 
      clear H1 H2. 
      assert (H1 := fun m t => IHt1_1 m t eq_refl). 
      assert (H2 := fun m t => IHt1_2 m t eq_refl). 
      clear - H1 H2. intros m t2 _. 
      induction t2 as [ x | m s1 IH1 s2 IH2 ]. simpl. specialize (H1 _ (L  x)); specialize (H2 _ (L  x) ). simpl in *. rewrite H1, H2; trivial. 
      simpl.                                                                                      
      rewrite IH1. simpl. rewrite IH2. trivial. 
  Qed. 

  Require Import Equality. 
  Lemma label_x_I_leq : forall n (t2: tree bool n) m (t1 : tree bool m), label t2 = I -> t1 /<=\ t2 = true. 
  Proof. 
    
    induction t2. 
    - simpl. destruct x; try discriminate. 
      intros m t1 _. induction t1. 
      destruct x; reflexivity. 
      simpl. rewrite IHt1_1, IHt1_2. reflexivity. 
    - simpl. intros. 
      
      destruct (label t2_1) eqn: H1; try discriminate;
      destruct (label t2_2) eqn: H2; try discriminate. clear H.  
      rewrite Bool.andb_true_iff. intuition. 
  Qed. 
  Hint Resolve label_O_x_leq label_x_I_leq. 
  
  Lemma tree_left_le_false : forall n (t: tree bool n), 
                               (t /<= false) = true -> 
                               label t = O.
  Proof.
    induction t. 
    destruct x; simpl; auto. discriminate. 
    simpl. intros H.  rewrite Bool.andb_true_iff in H. destruct H.  
    specialize (IHt1 H); specialize (IHt2 H0); 
    intuition. 
    repeat match goal with 
             | H : label ?t = ?x |- _ => rewrite H; clear H
           end; simpl; auto.  
  Qed.   

  Lemma tree_le_OI : forall n (s : tree bool n), 
                     forall m (t : tree bool m),
                       t /<=\ s = true -> 
                       label s = OI \/ label s = O  -> 
                       label t = O.
  Proof.      
    induction s.
    + simpl. destruct x; intuition;  try discriminate. 
      auto using tree_left_le_false. 
    + simpl; intros. 
      rewrite Bool.andb_true_iff in H. destruct H.
      specialize (IHs1 _ _ H).         specialize (IHs2 _ _ H1). 
      destruct H0;
        destruct (label s1) eqn: Hs1; destruct (label s2) eqn: Hs2; simpl in H0; try discriminate. intuition. intuition. intuition. intuition. 
      
  Qed. 
  
  Lemma sorted_label_disj : forall n t, tsorted n t -> 
                                   label t = O \/ label t = OI \/ label t = I. 
  Proof. 
    induction t. simpl in *. destruct x; auto. 
    simpl. intros H; inversion H.
    injectT. 
    intuition;
      try solve [repeat match goal with 
                          | H : label ?t = ?x |- _ => rewrite H; clear H
                        end; simpl; auto].
    exfalso; apply tree_le_OI in H5 ;[congruence | auto].
    exfalso; apply tree_le_OI in H5 ;[congruence | auto].
    exfalso; apply tree_le_OI in H5 ;[congruence | auto].
    exfalso; apply tree_le_OI in H5 ;[congruence | auto].
  Qed. 

  (** converse operation on labels *)
  Definition label_opp l :=
    match l with 
      | IO => OI | OI => IO | l => l
    end. 
  
  (** [label] commutes with [reverse], upto [label_opp] *)
  Lemma label_reverse n t : label (reverse _  n t) = label_opp (label t). 
  Proof. 
    induction t. 
    destruct x; reflexivity. 
    simpl; rewrite IHt1, IHt2. destruct (label t1); destruct (label t2); reflexivity. 
  Qed. 
  
  Lemma label_opp_move : forall l r, label_opp l = r <-> l = label_opp r. 
  Proof. 
    destruct l; destruct r; simpl in *; intuition congruence. 
  Qed. 

  Lemma sorted_down_label_disj : forall n t, tsorted n (reverse _ _ t) -> 
                                        label t = O \/ label t = IO \/ label t = I. 
  Proof. 
    induction t.
    +  simpl in *. destruct x; auto. 
    +  simpl. intros H; inversion H. injectT.
       intuition;
         try solve [repeat match goal with 
                             | H : label ?t = ?x |- _ => rewrite H; clear H
                           end; simpl; auto]; exfalso; apply tree_le_OI in H5; 
         repeat 
           match goal with 
             | H: label (reverse _ ?n ?t) = ?l |- _  => rewrite label_reverse in H; 
                                                      rewrite label_opp_move in H;
                                                      simpl in H
           end; try congruence;       
       rewrite label_reverse, ? label_opp_move; simpl; auto. 
  Qed. 
  
  (** a sequence is bitonic when its label is not [W] *)
  Definition bitonic {n} (t : tree bool n) := 
    match label t with 
      | W => false
      | _ => true
    end. 
  
  
  Lemma sorted_sorted_down_bitonic n (t1 t2 : tree bool n) : 
    tsorted n t1 -> tsorted n (reverse _ _ t2) -> 
    bitonic (N  _ t1 t2) = true. 
  Proof. 
    intros H1 H2. apply sorted_label_disj in H1.
    apply sorted_down_label_disj in H2. 
    unfold bitonic. simpl. 
    intuition; 
      repeat match goal with 
               | H : label ?t = ?l |- _ => rewrite H; clear H
             end; reflexivity. 
  Qed. 
  
  Section mms. 
    (** Some proofs about the min_max_swap function *)  
    
    Lemma tree_O_inversion : forall t : tree bool 0, exists x, t = L  x. 
      dependent destruction t. 
      exists x. 
      reflexivity. 
    Qed. 
    
    Lemma cmp_correct : forall (x y: bool), cmp x y = (min x y, max x y). 
    Proof. 
      intros; reflexivity. 
    Qed.
    
    Ltac init := 
      repeat match goal with 
               | H : tree bool 0 |- _ =>                            
                 let foo := fresh  in 
                 assert (foo := tree_O_inversion H); 
                   destruct foo; subst
               | H : bool |- _ => destruct H
               | |- _ -> _=> intros H; try discriminate; simpl              
             end; auto. 
    
    Arguments min_max_swap {A} {_} n _ _. 
    Arguments merge {A} {_} n _.
    
    Lemma label_min_max_swap_O_x n (l r: tree bool n) : 
      label l = O -> 
      let (a,b)  := min_max_swap n l r in 
      label a = O /\ label b = label r. 
    Proof. 
      induction n. 
      - init. 
      - simpl. 
        intros H. 
        dependent destruction l. simpl in H. 
        destruct (label l1) eqn:Hl; 
          destruct (label l2) eqn:Hr; simpl; try discriminate.        
        repeat match goal with 
                   H : label ?l = O |- context [min_max_swap ?n ?l ?r] =>            
                   let Heq := fresh in 
                   destruct (min_max_swap n l r) as [? ?] eqn:Heq ;
                     let H' := fresh in assert (H' := IHn l r H);
                                       rewrite Heq in H'
                                                        
               end; simpl; intuition;         try solve [repeat match goal with 
                                                                  | H : label ?x = _ |- _ => rewrite H in *; clear H
                                                                end; simpl; auto]. 
        rewrite H5, H6. clear. dependent destruction r; reflexivity. 
    Qed.     
  
    Lemma label_min_max_swap_I_x n (l r: tree bool n) : 
      label l = I -> 
      let (a,b)  := min_max_swap n l r in 
      label a = label r /\ label b = I. 
    Proof. 
      induction n. 
      - init.  
      - simpl. 
        intros H. 
        dependent destruction l. simpl in H. 
        destruct (label l1) eqn:Hl; 
        destruct (label l2) eqn:Hr; simpl; try discriminate.        
        repeat 
          match goal with 
              H : label ?l = I |- context [min_max_swap ?n ?l ?r] =>            
              let Heq := fresh in 
              destruct (min_max_swap n l r) as [? ?] eqn:Heq ;
                let H' := fresh in assert (H' := IHn l r H);
                                  rewrite Heq in H'
                                                   
          end; simpl; intuition;         try solve [repeat match goal with 
                                                             | H : label ?x = _ |- _ => rewrite H in *; clear H
                                                           end; simpl; auto]. 
        rewrite H4, H1. clear. dependent destruction r; reflexivity. 
    Qed.     
    
    Lemma label_min_max_swap_x_I n (l r: tree bool n) : 
      label r = I -> 
      let (a,b)  := min_max_swap n l r in 
      label a = label l /\ label b = I. 
    Proof. 
      induction n. 
    - init.  
    - simpl. 
      intros H. 
      dependent destruction r. simpl in H. 
      destruct (label r1) eqn:Hl; 
        destruct (label r2) eqn:Hr; simpl; try discriminate.        
      repeat 
        match goal with 
            H : label ?r = I |- context [min_max_swap ?n ?l ?r] =>            
            let Heq := fresh in 
            destruct (min_max_swap n l r) as [? ?] eqn:Heq ;
              let H' := fresh in assert (H' := IHn l r H);
                                rewrite Heq in H'
                                                 
        end; simpl; intuition;         try solve [repeat match goal with 
                                                           | H : label ?x = _ |- _ => rewrite H in *; clear H
                                                         end; simpl; auto]. 
      rewrite H4, H1. clear. dependent destruction l; reflexivity. 
    Qed. 
    
    Lemma label_min_max_swap_x_O n (l r: tree bool n) : 
      label r = O -> 
      let (a,b)  := min_max_swap n l r in 
      label a = O /\ label b = label l. 
    Proof. 
      induction n. 
      - init.  
      - simpl. 
        intros H. 
        dependent destruction r. simpl in H. 
        destruct (label r1) eqn:Hl; 
          destruct (label r2) eqn:Hr; simpl; try discriminate.        
        repeat 
          match goal with 
              H : label ?r = O |- context [min_max_swap ?n ?l ?r] =>            
              let Heq := fresh in 
              destruct (min_max_swap n l r) as [? ?] eqn:Heq ;
                let H' := fresh in assert (H' := IHn l r H);
                                  rewrite Heq in H'
                                                   
          end; simpl; intuition;         try solve [repeat match goal with 
                                                             | H : label ?x = _ |- _ => rewrite H in *; clear H
                                                           end; simpl; auto]. 
        rewrite H5, H6. clear. dependent destruction l; reflexivity. 
    Qed. 
    
    Lemma label_min_max_swap_OI_IO n ( l r : tree bool n) :
      label l = OI -> label r = IO -> 
      let (a,b) := min_max_swap n l r in 
      (label a = O /\ label b = I) \/
      (label a = O /\ label b = IOI) \/
      (label a = OIO /\ label b = I).
    Proof.  
      revert l r.  
      induction n.  
      - dependent destruction l. simpl; destruct x; discriminate. 
      - intros l r; dependent destruction l; dependent destruction r. 
        simpl. 
        destruct (label l1) eqn:Hl1; 
          destruct (label l2) eqn:Hl2; simpl; try discriminate;
          destruct (label r1) eqn:Hr1; 
          destruct (label r2) eqn:Hr2; simpl; try discriminate;
          intros _ _;
          destruct (min_max_swap n l1 r1) as [a b] eqn: Hab;
          destruct (min_max_swap n l2 r2) as [c d] eqn: Hcd; 
          simpl;
          repeat match goal with 
                   | H : label ?l = I, 
                         H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                     apply (label_min_max_swap_I_x n l r) in H;
                       rewrite H1 in H; destruct H
                   | H : label ?l = O, 
                         H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                     apply (label_min_max_swap_O_x n l r) in H;
                       rewrite H1 in H; destruct H
                   | H : label ?r = I, 
                         H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                     apply (label_min_max_swap_x_I n l r) in H;
                       rewrite H1 in H; destruct H
                   | H : label ?r = O, 
                         H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                     apply (label_min_max_swap_x_O n l r) in H;
                       rewrite H1 in H; destruct H
                   | Hl : label ?l = OI, 
                          Hr : label ?r = IO, 
                               H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                     specialize (IHn _ _ Hl Hr);
                       rewrite H1 in IHn; intuition
             end; try congruence;
          try solve [repeat match goal with 
                              | H : label ?x = _ |- _ => rewrite H in *; clear H
                            end; simpl; auto]. 
    Qed. 
          
    
    Lemma label_min_max_swap_IO_OI n ( l r : tree bool n) :
      label l = IO -> label r = OI -> 
      let (a,b) := min_max_swap n l r in 
      (label a = O /\ label b = I) \/
      (label a = O /\ label b = IOI) \/
      (label a = OIO /\ label b = I).
    Proof. 
      revert l r.  
      induction n.  
      - dependent destruction l. simpl; destruct x; discriminate. 
      - intros l r; dependent destruction l; dependent destruction r. 
        simpl. 
        destruct (label l1) eqn:Hl1; 
          destruct (label l2) eqn:Hl2; simpl; try discriminate;
          destruct (label r1) eqn:Hr1; 
          destruct (label r2) eqn:Hr2; simpl; try discriminate;
          intros _ _;
          destruct (min_max_swap n l1 r1) as [a b] eqn: Hab;
          destruct (min_max_swap n l2 r2) as [c d] eqn: Hcd; 
          simpl;
        repeat match goal with 
                 | H : label ?l = I, 
            H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                   apply (label_min_max_swap_I_x n l r) in H;
                     rewrite H1 in H; destruct H
                 | H : label ?l = O, 
                       H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                   apply (label_min_max_swap_O_x n l r) in H;
                     rewrite H1 in H; destruct H
                 | H : label ?r = I, 
                       H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                   apply (label_min_max_swap_x_I n l r) in H;
                     rewrite H1 in H; destruct H
                 | H : label ?r = O, 
                       H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                   apply (label_min_max_swap_x_O n l r) in H;
                     rewrite H1 in H; destruct H
                 | Hl : label ?l = IO, 
                        Hr : label ?r = OI, 
                             H1 : min_max_swap ?n ?l ?r = _ |- _ => 
                   specialize (IHn _ _ Hl Hr);
                     rewrite H1 in IHn; intuition
               end; try congruence;
        try solve [repeat match goal with 
                            | H : label ?x = _ |- _ => rewrite H in *; clear H
                          end; simpl; auto]. 
    Qed. 
    
    Lemma bitonic_min_max_swap n l r :
      bitonic (N n  l r) = true -> 
      let (a,b) := (min_max_swap  _ l r) in 
      bitonic a = true /\
      bitonic b = true /\
      a /<=\ b = true. 
    Proof. 
      induction n. 
      - unfold bitonic; simpl.
        dependent destruction l; dependent destruction r; destruct x; destruct x0; simpl; 
        try discriminate; compute; intuition. 
      - unfold bitonic.  replace (label (N (S n) l r)) with (compose (label l) (label r)) by reflexivity;
        destruct (label l) eqn:Hl; 
          destruct (label r) eqn:Hr; try discriminate; intros H; compute in H; 
        try 
          (clear IHn; match goal with 
             | H : label l = O |- _ => 
               apply (label_min_max_swap_O_x _ _ r) in H  
             | H : label l = I |- _ => 
               apply (label_min_max_swap_I_x _ _ r) in H
             | H : label r = O |- _ => 
               apply (label_min_max_swap_x_O _ l) in H
             | H : label r = I |- _ => 
               apply (label_min_max_swap_x_I _ l) in H          
           end; 
           destruct (min_max_swap _ l r) as [a b] eqn: Hab;
           match goal with 
               H : _ /\ _ |- _ =>  destruct H as [Hl1 Hl2]; rewrite Hl1, Hl2
           end; 
           match goal with 
             | H : label ?t = ?l |- _ => rewrite H; intuition
           end).
        (* interesting cases: the trees have label IO and OI *)
        pose proof (label_min_max_swap_OI_IO _ l r Hl Hr).        
        destruct (min_max_swap _ l r) as [a b] eqn:Hab. 
        intuition try solve [repeat match goal with 
                                      | H : label ?x = _ |- _ => rewrite H in *; clear H
                                    end; simpl; auto]. 
        pose proof (label_min_max_swap_IO_OI _ l r Hl Hr).        
        destruct (min_max_swap _ l r) as [a b] eqn:Hab. 
        intuition try solve [repeat match goal with 
                                      | H : label ?x = _ |- _ => rewrite H in *; clear H
                                    end; simpl; auto]. 
    Qed. 
    
    Section misc. 
      
      (** Various lemmas that relate operations on sequenes, and their sortedness *)
      Lemma tree_le_N_left n t1 t2 : forall  m (t: tree bool m), 
                                       N n t1 t2 /<=\ t = true -> 
                                       t1 /<=\ t = true /\ t2 /<=\ t = true. 
      Proof. 
        induction m. 
        - intros; init; simpl in *; apply Bool.andb_true_iff in H; intuition. 
        - intros. dependent destruction t.  simpl in *. 
          rewrite ? Bool.andb_true_iff in *. 
          destruct H as [H1 H2].  apply IHm in H1; apply IHm in H2.  
          intuition. 
      Qed. 
      
      Lemma tree_le_N_left' n t1 t2 m (t: tree bool m): 
        t1 /<=\ t = true -> t2 /<=\ t = true ->         N n t1 t2 /<=\ t = true.
      Proof.
        induction m. 
        - intros; init; simpl in *; apply Bool.andb_true_iff; intuition. 
        - intros. dependent destruction t.  simpl in *. 
          rewrite ? Bool.andb_true_iff in *. 
          intuition. 
      Qed. 
        
      Hint Resolve tree_le_N_left' .
      
      Lemma tree_le_N_right n t1 t2 m (t: tree bool m): 
        t /<=\ N n t1 t2 = true -> 
            t /<=\ t1 = true /\ t /<=\ t2 = true. 
      Proof. 
        induction m. 
        - intros; init; simpl in *; apply Bool.andb_true_iff in H; intuition. 
        - intros. dependent destruction t.  simpl in *. 
          apply Bool.andb_true_iff in H; intuition;
          apply IHm in H0; 
          apply IHm in H1; 
          apply Bool.andb_true_iff; intuition. 
      Qed. 
      
      Lemma tree_le_N_right' n t1 t2 m (t: tree bool m): 
            t /<=\ t1 = true -> t /<=\ t2 = true -> 
            t /<=\ N  n t1 t2 = true.
      Proof. 
        induction m. 
        - intros; init; simpl in *; apply Bool.andb_true_iff; intuition. 
        - intros. dependent destruction t.  simpl in *. 
          rewrite ? Bool.andb_true_iff in *. 
          intuition. 
      Qed. 
      Hint Resolve tree_le_N_right' .
      

      Lemma tree_le_min_max_swap_left m (t : tree bool m) : forall n t1 t2, 
                                                              t1 /<=\ t = true -> t2 /<=\ t = true ->
                                                              let (a,b) := (min_max_swap n t1 t2) in 
                                                              a /<=\ t = true /\ b /<=\ t = true. 
      Proof. 
        induction n; dependent destruction t1; dependent destruction t2.  
        - destruct x; destruct x0; simpl;
          simpl; auto. 
        - intros. simpl. 
          destruct (min_max_swap _ t1_1 t2_1) as [a b] eqn:Hab. 
          destruct (min_max_swap _ t1_2 t2_2) as [c d] eqn:Hcd.
          apply tree_le_N_left in H. 
          apply tree_le_N_left in H0. destruct H; destruct H0. 
          pose proof (IHn t1_1 t2_1 H H0). rewrite Hab in H3. 
          pose proof (IHn t1_2 t2_2 H1 H2). rewrite Hcd in H4. 
          intuition. 
      Qed. 
      
      Lemma tree_le_min_max_swap_right m (t : tree bool m) : forall n t1 t2, 
                                                               t /<=\ t1 = true -> t /<=\ t2 = true ->
                                                               let (a,b) := (min_max_swap n t1 t2) in 
                                                               t /<=\ a = true /\ t /<=\ b = true. 
      Proof. 
        induction n; dependent destruction t1; dependent destruction t2.  
        - destruct x; destruct x0; simpl;
          simpl; auto. 
        - intros. simpl. 
          destruct (min_max_swap _ t1_1 t2_1) as [a b] eqn:Hab. 
          destruct (min_max_swap _ t1_2 t2_2) as [c d] eqn:Hcd.
          apply tree_le_N_right in H. 
          apply tree_le_N_right in H0. destruct H; destruct H0. 
          pose proof (IHn t1_1 t2_1 H H0). rewrite Hab in H3. 
          pose proof (IHn t1_2 t2_2 H1 H2). rewrite Hcd in H4. 
          intuition. 
      Qed. 
      
      Lemma merge_le_left m (t2 : tree bool m) : forall n (t1 : tree bool n), 
                                              t1 /<=\ t2 = true -> merge _ t1 /<=\ t2 = true. 
      Proof. 
        induction n. 
        - dependent destruction t1. destruct x; simpl; auto. 
        - intros. simpl. 
          set (l := left  t1). set (r := right t1). 
          assert (t1 = N  _ l r). dependent destruction t1; reflexivity. 
          rewrite H0 in H. apply tree_le_N_left in H.  destruct H. 
          pose proof (tree_le_min_max_swap_left _ _ _ _ _ H H1). 
          destruct (min_max_swap _ l r) as [a b] eqn:Hab. 
          intuition. 
      Qed. 
      
      Lemma merge_le_right m (t2 : tree bool m) : forall n (t1 : tree bool n), 
                                              t2 /<=\ t1 = true -> t2 /<=\ merge  _ t1 = true. 
      Proof. 
        induction n. 
        - dependent destruction t1. destruct x; simpl; auto. 
        - intros. simpl. 
          set (l := left t1). set (r := right t1). 
          assert (t1 = N _ l r). dependent destruction t1; reflexivity. 
          rewrite H0 in H. apply tree_le_N_right in H.  destruct H. 
          pose proof (tree_le_min_max_swap_right _ _ _ _ _ H H1). 
          destruct (min_max_swap _ l r) as [a b] eqn:Hab. 
          intuition. 
      Qed. 
                                
    End misc. 
    
    (** Merging a bitonic sequence yields a sorted sequence  *)
    Lemma merge_sorted : forall n (t : tree bool n), bitonic t = true -> 
                                                tsorted _ (merge _ t).
    Proof. 
      induction n. 
      - intros. simpl. dependent destruction t.  apply tsorted_L. 
      - dependent destruction t. simpl. 
        intros H. 
        apply bitonic_min_max_swap in H. 
        destruct (min_max_swap n t1 t2) as [a b] eqn: Hab. 
        constructor. apply IHn. intuition.  
        intuition. 
        apply merge_le_left. apply merge_le_right. intuition. 
    Qed. 
    
    (** [sort] produces a sequence that is sorted *)
    Lemma sort_tsorted : forall n t , tsorted _ (sort _ _  n t). 
    Proof. 
      induction n. 
      - intros. simpl. dependent destruction t.  apply tsorted_L. 
      - dependent destruction t. simpl. 
        set (l :=  (sort bool _  n t1)). 
        set (r :=  (sort bool _  n t2)). 
        destruct (min_max_swap n l (reverse bool n r)) as [a b] eqn: Hab. 
        assert (bitonic (N n l (reverse bool n r))= true). 
        apply sorted_sorted_down_bitonic. apply IHn. 
        Lemma reverse_idempotent : forall n (t : tree bool n), reverse _ n ( reverse _ n t) = t. 
        Proof. 
          induction n.
          dependent destruction t. reflexivity. 
          intros; simpl. dependent destruction t.  simpl.  rewrite IHn.  rewrite IHn. reflexivity. 
        Qed. 
        rewrite reverse_idempotent. 
        apply IHn. 
        apply bitonic_min_max_swap in H. 
        rewrite Hab in H. 
        constructor; intuition. 
        apply merge_sorted. auto. 
        apply merge_sorted. auto. 
        apply merge_le_left. apply merge_le_right. intuition. 
    Qed.
  End mms.
  Print Assumptions sort_tsorted. 

  (** * Proof of the 0-1 principle

  We prove the 0-1 principle, to extend the proof of correctness of
  our sorting algorithm from boolean sequences to sequences of an
  arbitrary type. In order to stick with existing presentations, we
  proved the 0-1 principle on lists, and lift this results to our
  notion of sequences of length [2^n] *)

  (** We define what it means for a list to be sorted *)
  Inductive sorted {A} {O : order A} : list A -> Prop :=
  | sorted_nil : sorted nil
  | sorted_cons : forall t q, sorted q -> List.Forall (fun x => t <= x = true) q -> sorted (t::q).
  
  Module zero_one_principle. 
    Section inner. 
      Require Import Morphisms. 
      
      Coercion is_true (b : bool) : Prop := b = true. 
      
      (** We assume that we have a parametric sorting function that
      commutes with arbitrary monotone functions *)

      Variable sort : forall A, order A -> forall n, tree A n -> tree A n.
      Hypothesis H : forall n (t : tree bool n), tsorted n (sort _ bool_order n t).
      
      
      Hypothesis Hcommute : forall {A B} {PA : order A} {PB : order B} (f : A -> B) 
                              (Hf : monotone PA PB f), 
                            forall n t,
                              map f (sort A PA n t)  = sort B PB n (map f t). 

      
      
      (** If a list is not sorted, it means that one pair of
      consecutive elemnts is not in the right order *)

      Lemma not_sorted_inversion A (R: order A) : forall l, ~ sorted l -> 
                                                       exists l1 x y l2, 
                                                         l = List.app l1 (x :: y :: l2)%list /\ y < x .
      Proof.
        induction l. 
        - intros H1. 
          exfalso.  apply H1. constructor. 
        - intros.  destruct l as [ | t q]. 
          + exfalso. apply H0. constructor;  auto. constructor. 
          + destruct (t < a) eqn : Hlt. 
            exists nil; exists a; exists t; exists q.  simpl.  intuition. 
            assert (~sorted (t :: q)). 
            {
              clear IHl. intros Hf. apply H0. clear H0. 
              clear - Hlt Hf. assert (H : a <= t). clear - Hlt. 
              rewrite Bool.negb_false_iff in Hlt. auto.              
              clear Hlt. 
              constructor. auto. inversion Hf. subst. clear - H H3.
              constructor. auto. 
              induction q. auto.
              inversion H3. subst. 
              constructor. eapply le_transitive; eauto. eauto. 
            }
            specialize (IHl H1).
            destruct IHl as [l1 [x  [y [l2 [IH1 IH2] ]]]].
            exists (a :: l1)%list; exists x; exists y; exists l2. rewrite IH1.  intuition. 
      Qed. 

      Lemma List'Forall_imply A (P Q : A -> Prop) (HPQ:forall x, P x -> Q x) : forall l, List.Forall P l -> List.Forall Q l.
      Proof. 
        induction l. easy.
        intros Hal. inversion Hal. subst. constructor; intuition.
      Qed.

          
      Lemma List'Forall_append A (P : A -> Prop) : forall l1 l2, List.Forall P l1 -> List.Forall P l2 -> 
                                                           List.Forall P (List.app l1 l2).
      Proof. 
        induction l1. 
        easy. 
        simpl. 
        intros. constructor. inversion H0; auto. apply IHl1.  inversion H0; auto. auto. 
      Qed. 

      Lemma List'Forall_append_inv A (P : A -> Prop) : forall l1 l2, List.Forall P (l1 ++ l2) -> List.Forall P l1 /\ List.Forall P l2. 
      Proof.
        induction l1. simpl. auto. 
        intros. simpl in *. inversion H0. subst. intuition. apply IHl1 in H4. constructor; intuition.
        apply IHl1 in H4. intuition. 
      Qed. 
      
      (** Lemmas about being sorted, and various operations  *)
      Lemma not_sorted_app : forall l1 l2, ~ sorted l2 ->  ~ sorted (List.app l1 l2).
      Proof. 
        induction l1. simpl. tauto. 
        simpl. intros l2 Hl2 Hf.  
        inversion Hf. subst.
        apply (IHl1 l2 Hl2 H2). 
      Qed. 

      Lemma sorted_app A (R : order A):
        forall l1 l2, sorted l1 -> sorted l2 ->
                 [:: l1 <= l2 ] -> 
                 sorted (l1 ++ l2). 
      Proof. 
        induction l1. 
        - easy. 
        - intros. simpl. constructor. apply IHl1. inversion H0; auto.   eauto. 
          eapply List'Forall_imply. 2: apply H2. 
          clear. intros. simpl in *. 
          revert x H. induction l1. constructor.
          intros. constructor. inversion H. subst. inversion H3; subst. subst. auto. 
          inversion H. subst. inversion H3. subst. auto. 
          apply List'Forall_append.
          inversion H0; auto. 
          
          eapply List'Forall_imply. 2: apply H2. 
          intros. simpl in H3. inversion H3.  subst. auto. 
      Qed. 
  
      Lemma sorted_append_inversion A (O : order A): forall (l1 l2 : list A), sorted (l1 ++ l2) -> (sorted l1 /\ sorted l2). 
      Proof. 
        induction l1. simpl. intuition. constructor. 
        simpl. intros. inversion H0. subst. apply IHl1 in H3. split; intuition. 
        constructor. auto. 
        apply List'Forall_append_inv in H4.  intuition. 
      Qed.

      Lemma List'Forall_commute A (f : A -> A -> Prop )l1 l2 :
        List.Forall (fun x => List.Forall (fun y => f x y) l1) l2 
        <-> List.Forall (fun y => List.Forall (fun x => f x y) l2) l1. 
      Proof.
        repeat setoid_rewrite List.Forall_forall. 
        intuition. 
      Qed.

      Lemma sorted_append_order A (O : order A) : forall l1 l2, 
                                                    sorted (l1 ++ l2) -> 
                                                    [:: l1 <= l2].
      Proof. 
        induction l1. 
        - simpl. intros l2 _. induction l2; auto. 
        - simpl. intros. inversion H0. subst. apply IHl1 in H3. clear - H3 H4. 
          apply List'Forall_append_inv in H4 . destruct H4. 
          
          rewrite List'Forall_commute. constructor. auto. 
          rewrite List'Forall_commute. apply H3. 
      Qed. 
      
      Lemma Tree'Forall_List'Forall A (P : A -> Prop) (Q : A -> bool) 
            (IH : forall a, Q a = true -> P a):
        forall n (t : tree A n),
          Forall t Q -> List.Forall P (list_of_tree A t).
      Proof.
        induction n. dependent destruction t. simpl. intuition. 
        dependent destruction t. simpl. intros. apply Bool.andb_true_iff in H0. destruct H0. 
        apply List'Forall_append. auto. auto. 
      Qed. 
      
      Lemma List'Forall_Tree'Forall A (P : A -> Prop) (Q : A -> bool) 
            (IH : forall a, P a -> Q a = true ):
        forall n (t : tree A n),
          List.Forall P (list_of_tree A t) -> Forall t Q.
        induction n; dependent destruction t; simpl. inversion 1. subst. apply IH. auto. 
        intros. apply List'Forall_append_inv in H0. intuition.  apply Bool.andb_true_iff. intuition. apply IHn. auto. apply IHn. auto. 
      Qed. 
      
      Lemma tsorted_sorted_list_of_tree A (R: order A): forall n (t : tree A n ), tsorted n t <-> sorted (list_of_tree A t). 
      Proof. 
        induction n. 
        - dependent destruction t.  simpl. intuition. constructor. constructor.  auto.
          inversion H0. subst. constructor. 
        - dependent destruction t. split; intros. 
          inversion H0; injectT. 
          simpl.
          apply sorted_app. rewrite <- IHn.  auto. rewrite <- IHn. auto. 
          clear - H6. 
          
          eapply Tree'Forall_List'Forall. 2: apply H6. simpl. intros. 
          eapply Tree'Forall_List'Forall. 2: apply H. simpl. intros. auto. 
          
          constructor. rewrite IHn. simpl in H0. 
          
          apply sorted_append_inversion in H0. intuition.  
          rewrite IHn.       apply sorted_append_inversion in H0.
          intuition.  
          
          simpl in H0. 
          
          
          apply sorted_append_order in H0. 
          clear - H0. 
          eapply List'Forall_Tree'Forall. 2: apply H0. simpl. 
          intros. eapply List'Forall_Tree'Forall. 2: apply H. 
          simpl.
          auto. 
      Qed. 
      
      (** We are now ready for the proof of the 0-1 principle  *)
      Theorem zero_one_principle :
        forall A (R : order A) n t, tsorted n (sort A R  n t) .
      Proof.
        Require Import Classical.
        (** We rely on a classical proof, via a double negation elimination *)

        apply NNPP. 
        intros H1.
        apply not_all_ex_not in H1. 
        destruct H1 as [A H1].
        apply not_all_ex_not in H1. 
        destruct H1 as [R H1].
        apply not_all_ex_not in H1. 
        destruct H1 as [n H1].
        apply not_all_ex_not in H1. 
        destruct H1 as [t H1].
    
        (** We have to prove that the hypothesis that there exists a type [A] and a list of
   [A] that our candidate algorithm fails to sort is absurd.       *)

        rewrite tsorted_sorted_list_of_tree in H1.                 
        
        (** From such a list, we extract a pair of consecutive
        elements that are not in the right order*)

        apply not_sorted_inversion in H1.
        
        destruct H1 as [l1 [x [y [ l2 [H1 H2] ]]]].
        
        (** We build a monotone function [f] from [A] to [Bool]*)
        set (f := fun (c : A) => if c < x then false else true).
        set (b := sort A R n t) in *. 
        
        assert (Hf : monotone _ _ f).
        {
          constructor.
          intros; subst. auto. 
          clear - f. intros. unfold f.
          destruct  (le x a) eqn : Ha;
            destruct  (le x b) eqn : Hb; trivial.
          exfalso.
          pose proof (le_transitive _ _ _ Ha H). congruence.
        } 
        
        (** [f] is monotone, thus it commutes with the sort
        function. We go on to prove that the image of our list
        w.r.t. to [f] is not sorted.  *)

        assert (~ tsorted _ (map f b)).
        {
          rewrite tsorted_sorted_list_of_tree. 
          Lemma map_commute A B (f :A -> B) n (t : tree A n) : 
            list_of_tree _ (map f t) = List.map f (list_of_tree _ t). 
          Proof. 
            induction n. 
            dependent destruction t. simpl. reflexivity. 
            simpl. repeat rewrite IHn. dependent destruction t. simpl. rewrite List.map_app. reflexivity. 
          Qed.
          rewrite map_commute. 
          rewrite H1. 
          rewrite List.map_app. simpl. 
          apply not_sorted_app. intros Hs. 
          inversion Hs;  subst.
          inversion H5; subst. 
          clear - H6 H2 f Hf.  
          
          assert (Hx : f x = true ). unfold f.  rewrite le_reflexive. reflexivity. 
          assert (Hy : f y = false). unfold f. rewrite H2. reflexivity. 
          rewrite Hx, Hy in H6. simpl in H6. discriminate. 
        }      
        
        (** We now have a list of booleans that is not sorted, which
        contradicts our hypothesis that our candidate sorting
        algorithm succesfully sorts lists of Booleans *)

        apply H0.  unfold b. 
        
        rewrite (Hcommute A bool _ bool_order). apply H. 
        apply Hf. 
      Qed. 
  
    End inner. 
  End zero_one_principle.   
  
  (** We shall now prove that the various functions that are used in
  the definition of our candidate sorting algorithm commute with
  monotone functions. *)
  
  Section commutation_lemmas.
    Variable A B : Type. 
    Variable f : A -> B. 
    Variable (PA : order A) (PB : order B). 
    Hypothesis H : monotone PA PB f. 
    
    Lemma reverse_commute : 
      forall (n : nat) (t : tree A n),
        reverse B n (map f t) = map f (reverse A n t).  
    Proof. 
      induction n; dependent destruction t. 
      - reflexivity. 
      - simpl. rewrite ? IHn. reflexivity. 
    Qed. 
    
    Lemma min_max_swap_commute :
      forall (n : nat) (t1 t2 : tree A n) ,
        (let (a,b) := (min_max_swap A PA n t1 t2) in 
         (map f a, map f b)) = min_max_swap B PB n (map f t1) (map f t2). 
    Proof. 
      induction n; dependent destruction t1; dependent destruction t2. 
      simpl. 
      
      {
        rewrite (min_commute PA PB), (max_commute PA PB). reflexivity. auto. auto. 
      }
      simpl. repeat rewrite <- IHn. 
      repeat match goal with 
                 |- context [min_max_swap ?A ?PA ?b ?l ?r] => destruct (min_max_swap A PA b l r)
             end. simpl. reflexivity. 
    Qed.
    
    Lemma merge_commute :
      forall (n : nat) (t : tree A n),
        merge B PB n (map f t) = map f (merge A PA n t). 
    Proof. 
      induction n; dependent destruction t. 
      - reflexivity. 
      - simpl. rewrite <- min_max_swap_commute. 
        destruct (min_max_swap A PA n t1 t2). simpl. rewrite IHn. rewrite IHn. reflexivity.
    Qed. 
  End commutation_lemmas. 
  
  (** * Our sort function is correct
   We gather all the previous intermediate lemmas to prove that our
   parametric sorting function is correct *)

  Theorem sort_correct A {O : order A} cmp n (t: tree A n) : 
    tsorted _ (sort _ cmp n t). 
  Proof. 
    apply zero_one_principle.zero_one_principle. 
    apply sort_tsorted. 
    {  
      clear. 
      intros.
      induction n; dependent destruction t. 
      - reflexivity. 
      - simpl. 
        destruct ( min_max_swap A PA n (sort A PA n t1)
                                (reverse A n (sort A PA n t2))) as [a b] eqn : Hab. 
        simpl. 
        destruct (min_max_swap B PB n (sort B PB n (map f t1))
                               (reverse B n (sort B PB n (map f t2)))) as [c d] eqn : Hcd. 
        simpl. 
        repeat rewrite <- IHn  in Hcd. 
        repeat rewrite reverse_commute in Hcd.       
        rewrite <- (min_max_swap_commute _ _ f PA PB) in Hcd. rewrite Hab in Hcd.  inject Hcd. 
        repeat erewrite <- merge_commute by eassumption.  reflexivity.
        auto. 
    }
  Qed. 
End Spec. 

(** * Definition of the sorting core 
 
     We mimic the definition that we used in the specification with
     the following difference. A circuit generator takes as input a
     sequence of variables (of length [2^n]), and produces a circuit
     with a return type [domain n] that corresponds to a
     deep-embedding of [tree n] in our data-type of circuits.

*)

Module Circuit. 
  
  Section t. 
    Require Import Front.
    
  Variable A : type.
  Variable Var : type -> Type. 

  Notation T n := (tree (expr Var A) n). 
  Notation "x ⊗ y" := (Ttuple [x;y]) (at level 74). 
  
  Fixpoint domain n := 
    match n with 
      | 0 => A
      | S n => (domain n) ⊗ (domain n)
    end. 
    
  Definition C n := action nil Var (domain n). 
  
  Fixpoint reverse n (t : T n) : C n  :=
    match t with 
      | L x => ret (x)
      | N n l r => 
        do r <- reverse n r;
        do l <- reverse n l;
        ret [tuple r, l]
    end%action.

  Definition leaf (l : T 0) : expr Var A := match l with
                                     | L x => x
                                   end.
  
  Definition left {n} (l : T (S n)) : T n :=
    match l with 
      | N _ l _ => l
    end.
 
  Definition right {n} (l : T (S n)) : T n := 
    match l with 
      | N _ _ r => r
    end. 
  
  (** The [cmp] parameter corresponds to the primitive compare and
  swap operation that is the basic block of our sorting network. *)
  Variable cmp : expr Var A -> expr Var A -> action nil Var (Ttuple [A ; A]). 
  
  Notation mk_N x y := ([tuple x,y])%expr.
  
  Notation "'do' x , y <- a ; b" := 
    (do na <- a;
     do x <- ret (Efst na);
     do y <- ret (Efst (Esnd na));
     b)%action
       (at level 200, x ident, y ident, a at level 100, b at level 200): action_scope.  

  Fixpoint min_max_swap n : forall (l r : T n), C (S n) :=
    match n return T n -> T n -> action nil Var ((domain n) ⊗ (domain n)) with 
      | 0 => fun l r => cmp (leaf l) (leaf r)
      | S n => fun l r => 
                do a,b <- min_max_swap n (left l) (left r);
                do c,d <- min_max_swap n (right l) (right r); 
                ret ([tuple mk_N a c, mk_N b d])
    end%action. 

  (* (*  The classic bind  *) *)
  (* Notation "'do' x <~ a ; b " := (Bind a (fun x =>  b))  *)
  (*                               (at level 200, x ident, a at level 100, b at level 200)  *)
  (*                                : action_scope.  *)

  Fixpoint rebind {U} n : expr Var (domain n) -> (T n -> action nil Var U) -> action nil Var U :=
    match n with 
      | 0 => fun t f => f (L t)  
      | S n => fun t f => 
                do a, b <- ret t;
                rebind n a (fun t1 =>
                              rebind n b (fun t2 =>
                                            f (N n t1 t2)
                                         )
                           )
    end%action. 

  Notation "'do' x <: a ; b" :=  
    ( 
     rebind _ a (fun x =>  b))%action 
      (at level 200, x ident, a at level 100, b at level 200) 
    : action_scope. 

    
  
  Fixpoint merge n: T n -> C n := 
    match n with 
      | 0 => fun t => ret (leaf t)
      | S k => fun t => 
                let l := left t in
                let r := right t in
                do a,b  <-  min_max_swap _ l r;
                do a <: a;      (* use an explicit reification step *)
                do b <: b;      (* use an explicit reification step *)
                do a <- merge _ a;
                do b <- merge _ b;
                ret (mk_N  a b)
    end%action. 
  
  
  Fixpoint sort n : T n -> C n :=
    match n with 
      | 0 => fun t => ret (leaf t)
      | S n => fun t => 
                let l := left t in 
                let r := right t in 
                do l <- sort _ l; 
                do r <- sort _ r; do r <: r;
                do r <- reverse _ r;                 
                do x <- ret (mk_N l r);
                rebind (S n) x (fun x => merge _ x)
    end%action. 
  End t.

  Definition output  (t : type) (A : action nil eval_type t) : 
    option (eval_type t) :=    
    match Sem.eval_action  A DList.DList.nil (Diff.init []%list)  with
      | Some p => Some (fst p)
      | None => None
    end. 

    
End Circuit.


Section proof. 
  (** * Proof of a particular instance of our sorter core: sorting machine words of a given size. *)
  
  Definition int_cmp_swap  {Var : type -> Type} n :=
    fun (x y : expr Var (Tint n)) => 
      (do c <- ret (x <= y)%expr;
       do min <- ret (Emux c x y)%expr;
       do max <- ret (Emux c y x)%expr;
       @Return nil _ _  [tuple min, max]
      )%action. 

  
  
  Variable size : nat. 
  Notation A := (Tint size).
  Notation xchg := (int_cmp_swap size).
  
  (** To argue about the semantics of our circuit, we fix a choice of Var as eval_type  *)
  Notation Var := eval_type.
  
  Instance word_order {n} : order (Word.T n).
  refine (mk_order _ Word.le _ _ _).
  apply Word.le_transitive.
  apply Word.le_total. 
  apply Word.le_antisym.
  Defined. 
  
  (** The specification of our sorting algorithm  *)
  Definition sort := Spec.sort (Word.T size) word_order. 

  (** The actual circuit definition  *)
  Notation csort n I := (Circuit.sort A eval_type xchg n (map (@Evar eval_type A) I)).
  
  (** The equivalence relation between the denotation of a [domain] and a [tree] *)
  Inductive R : forall n, Var (Circuit.domain A n) -> tree (Word.T size) n -> Prop := 
  | R_L : forall x, R 0 (x) (L x)
  | R_N : forall n l1 l2 r1 r2, 
            R n l1 l2 -> 
            R n r1 r2 -> 
            R (S n) (l1,(r1,tt)) (N n l2 r2).

  Notation "x == y" := (R _ x y) (at level 80).
  
  
  Lemma R_N_fst : forall n (e: eval_type (Circuit.domain A (S n))) a b, 
                    e == (N n a b) -> 
                    (@Tuple.fst type eval_type (Circuit.domain A n :: nil) _ e) == a.
  Proof. 
    inversion 1; injectT; easy. 
  Qed. 
  
  Lemma R_N_snd : forall n (e: eval_type (Circuit.domain A (S n))) a b, 
                    e == (N n a b) -> 
                    Tuple.fst (@Tuple.snd type eval_type (Circuit.domain A n :: nil) _ ( e)) == b.
  Proof. 
    inversion 1; injectT; easy. 
  Qed. 
  
  Hint Constructors R. 
  Ltac R_resolve :=
    match goal with 
      | H : Var (Ttuple [Circuit.domain A ?n; Circuit.domain A ?n]) |- _ => destruct H; R_resolve
      | H : Tuple.of_list _ _ |- _ => destruct H; R_resolve
      | H :  ( ?x , ?y ) == _  |- _ => apply R_N_fst in H; simpl in H; R_resolve
      | H :  ( ?x , ?y) == _  |- _ => apply R_N_snd in H; simpl in H; R_resolve
      | |- _ => eassumption
      | |- _ == _ => constructor; R_resolve
      | |- _ == _ => eapply R_N_fst; R_resolve
      | |- _ == _ => eapply R_N_snd; R_resolve
    end.  
        
  Hint Extern 1 (_ == _)  => R_resolve. 

  Require Import Equality. 
  
  Lemma diff_nil : (forall t : Diff.T []%list, t = Diff.init []%list).
  Proof. 
    dependent destruction t. compute.  reflexivity.
  Qed. 
  
  Ltac destruct_a_match H :=
    let  rec tac G :=
         match G with 
           | context [ match ?x with | _ => _ end] => tac x || destruct x eqn:H
         end
    in
    match goal with 
        |- ?G => tac G; try tauto
    end. 

  Ltac destruct_a_match' := let H := fresh in destruct_a_match H.
  
  Lemma output_bind t a : forall u b, Circuit.output u (do x <- a; b x)%action = 
                                 do x <- (Circuit.output t a);
                                 Circuit.output _ (b (Evar x)).
  Proof.
    induction a; intros. 
    - reflexivity.
    - unfold Circuit.output. simpl. unfold Sem.Dyn.Bind in *.  
      destruct_a_match'.
      destruct p. simpl. rewrite (diff_nil t0). simpl in *. 
      destruct_a_match'. simpl. destruct p. simpl in *. rewrite (diff_nil t1). 
      reflexivity. 
    - unfold Circuit.output.  simpl. destruct (eval_expr B e); simpl;  reflexivity. 
    - unfold Circuit.output.  simpl.
      symmetry; destruct_a_match'.  
      simpl. unfold Sem.Dyn.Bind. rewrite H.  destruct p0. simpl. 
      rewrite (diff_nil t). 
      reflexivity. 
      simpl. unfold Sem.Dyn.Bind. rewrite H. reflexivity. 
    - unfold Circuit.output. 
      simpl. unfold Sem.Dyn.OrElse, Sem.Dyn.Bind. 
      destruct_a_match'. simpl. destruct p. rewrite (diff_nil t0). simpl. reflexivity.
      destruct_a_match'. destruct p; simpl. rewrite (diff_nil t0). reflexivity.  
  Qed.

  Lemma output_rebind n e e': 
    e == e' ->
    forall u b, Circuit.output u (Circuit.rebind A Var n (Evar e) (fun x => b x)) =
           Circuit.output _ (b (map (@Evar eval_type A)e')).
  Proof. 
    intros H. 
    induction H. 
    - trivial.  
    - intros. simpl. 
      rewrite output_bind. simpl. 
      rewrite output_bind. simpl. 
      rewrite output_bind. simpl. 
      rewrite IHR1. rewrite IHR2. 
      reflexivity. 
  Qed. 

  Lemma output_reverse  n l :       
    match Circuit.output _ (Circuit.reverse A Var n (map Evar l)) with 
      | None => False
      | Some e => e == Spec.reverse _ n l
    end.  
  Proof. 
    induction l. 
    simpl; constructor. 
    simpl in *. rewrite output_bind.
    intro_do x2 H2. rewrite output_bind.  intro_do x1 H1. 
    constructor; auto. 
    auto. 
    auto. 
  Qed.

  Lemma output_bind' t a : forall u b, Circuit.output u (do x <~ a; b x)%action = 
                                  do x <- (Circuit.output t (ret a)%action);
                                  Circuit.output _ (b (Evar x)).
  Proof. 
    intros. unfold Bind'. rewrite <- output_bind. reflexivity.  
  Qed. 

  Ltac destruct_a_let := 
    match goal with 
        |- context [(let (_,_) := ?a in _)] => destruct a as [? ?] eqn:? 
    end.
      
  Lemma output_min_max_swap n : forall l1 l2,
    match Circuit.output _ (Circuit.min_max_swap A Var xchg 
                                                 n (map Evar l1) (map Evar l2)) with 
      | None => False
      | Some e => let (a,b) := Spec.min_max_swap _ _ n l1 l2 in e ==  N _ a b
    end.  
  Proof. 
    induction n; dependent destruction l1; dependent destruction l2;simpl.
    -  unfold min, max. unfold le, word_order. 
       destruct (Word.le x x0) eqn:H. 
       repeat constructor. 
       repeat constructor. 
    - repeat 
        first 
        [
          rewrite output_bind ; let x := fresh in let H := fresh in intro_do x H; trivial
        | rewrite output_bind'; let x := fresh in let H := fresh in intro_do x H; trivial
        ];
      repeat match goal with 
               | H : context [Circuit.min_max_swap A Var xchg n (map Evar ?l1) (map Evar ?l2)] |- _
                 => 
                 let H1 := fresh in 
                 let H2 := fresh in 
                 assert(H1 := IHn l1 l2);
                   simpl in H1;
                   simpl in H; rewrite H in H1; clear H
             end; clear IHn. 
      repeat match goal with 
                 H : context [?x] |- context [let (_,_) := ?x in _] => destruct x eqn:?; trivial
             end;
      repeat match goal with 
          | H : context [Return _]  |- _ => compute in H; inject H
        end. 
      R_resolve. 
      trivial. 
      compute in H4. discriminate. 
      compute in H2; discriminate. 
      trivial.
  Qed.
  
  Lemma output_merge n l:         
    match Circuit.output _ (Circuit.merge A Var xchg n (map Evar l)) with 
      | None => False
      | Some e => e == Spec.merge _ _ _ (l)
    end.  
  Proof. 
    revert l. 
    induction n. 
    - dependent destruction l; constructor.  
    - dependent destruction l. 
      simpl. 
      repeat 
        (first 
        [
          rewrite output_bind ; let x := fresh in let H := fresh in intro_do x H; trivial
        | rewrite output_bind'; let x := fresh in let H := fresh in intro_do x H; trivial
        ]);  
        repeat match goal with 
                 | H : context [Return _]  |- _ => compute in H; try discriminate; inject H
               end. 
      Focus 2. 
      
      Ltac use_a_match_theorem_2 thm e l1 l2 :=
        match type of thm with 
          | (forall x y, match @?X x y with _ => _ end) =>
            let Y :=  eval simpl in  (X l1 l2) in
            let H := fresh in 
            assert (H := thm l1 l2);
            simpl in H; simpl in e;
            rewrite e in H
        end.

      Ltac use_a_match_theorem_1 thm e l1  :=
        match type of thm with 
          | (forall x , match @?X x  with _ => _ end) =>
            let Y :=  eval simpl in  (X l1) in
            let H := fresh in 
            assert (H := thm l1);
            simpl in H; simpl in e;
            rewrite e in H
        end.                   
      use_a_match_theorem_2 ( output_min_max_swap n) H0 l1 l2.  
      auto. 
      use_a_match_theorem_2 (output_min_max_swap n) H0 l1 l2. clear H0. 
      revert H1. destruct_a_let. intros. 
      erewrite output_rebind by eauto. 
      erewrite output_rebind by eauto.  
      rewrite output_bind. intro_do x1 Hx1.  
      rewrite output_bind. intro_do x2 Hx2.  
      simpl in *. 
      use_a_match_theorem_1 (IHn ) Hx1 t.  clear Hx1. 
      use_a_match_theorem_1 (IHn ) Hx2 t0.  clear Hx2. 
      R_resolve. 
      use_a_match_theorem_1 (IHn ) Hx2 t0.   auto. 
      use_a_match_theorem_1 (IHn ) Hx1 t.   auto. 
  Qed. 

      

  Lemma equiv_sort n  
        (I : tree (Var A) n) :
    match Circuit.output _ (csort n I) with 
      | None => False
      | Some e => e == (sort n I)
    end. 
  Proof.
    induction n.
    - dependent destruction I. constructor.   
    - simpl. 
      Ltac t IHn := 
        match goal with 
            |- context [Circuit.output ?t (Bind' _ _ )] => rewrite output_bind
          | |- context [Circuit.output ?t (Bind _ _ )] => rewrite output_bind' 
          | |- context [Circuit.output ?t (csort ?n ?I)] => 
            let H1 := fresh "H" in 
            let H2 := fresh "H" in 
            assert (H1 := IHn I);
            destruct (Circuit.output _ (csort n I)) as [?|] eqn:H2; 
              [simpl in H2; simpl; rewrite H2; simpl|tauto]
          | |- context [Circuit.output ?t (Circuit.reverse _ _  ?n (map Evar ?I))] => 
          let H1 := fresh "H" in 
          let H2 := fresh "H" in 
          assert (H1 := output_reverse n I);
            revert H1; destruct_a_match H2; intros H1; simpl
          | |- context [Circuit.output ?t (Circuit.merge _ _ _  ?n (map Evar ?I))] => 
          let H1 := fresh "H" in 
          let H2 := fresh "H" in 
          assert (H1 := output_merge n I);
            revert H1; destruct_a_match H2; intros H1; simpl; simpl in H2; rewrite H2; simpl
        end. 
      repeat (t IHn). 
      erewrite output_rebind by eauto. 
      repeat (t IHn).
      repeat (simpl; t IHn).
      simpl. 
      erewrite output_rebind by eauto. 
      simpl. 
      erewrite output_rebind by eauto. 
      simpl.
      
      t IHn.
      match goal with 
        |- context [Circuit.output ?t (Circuit.min_max_swap _ _ _ n 
                                                           (map Evar ?l1)
                                                           (map Evar ?l2)
                                     )] =>
        let H1 := fresh "H" in 
        let H2 := fresh "H" in 
        assert (H1 := output_min_max_swap n l1 l2);
          revert H1; destruct_a_match H2; intros H1; simpl; simpl in H2; rewrite H2; simpl
      end.
      t IHn. 
      simpl. 
      t IHn. 
      simpl. 
      
      destruct (       Spec.min_max_swap (Word.T size) word_order n 
             (sort n (left I))
             (Spec.reverse (Word.T size) n (sort n (right I)))) as [ a b] eqn : Hab.
      
      rewrite output_rebind with (e' := a). 
      rewrite output_rebind with (e' := b). 
      rewrite output_bind.
      simpl. 
      t IHn. t IHn. t IHn. simpl. 
      destruct_a_let. 
      simpl in *. 
      rewrite Hab in Heqp.  inject Heqp. eauto. 
      
      simpl in *. rewrite Hab in H5. eapply R_N_snd. R_resolve. 
      simpl in *. rewrite Hab in H5. eapply R_N_fst. R_resolve. 
  Qed. 

  Theorem circuit_sort_correct' n (I : tree (Var A) n) : 
    match Circuit.output _ (csort n I) with 
      | None => False
      | Some out => out == (sort n I) /\ Spec.tsorted n (sort n I)
    end. 
  Proof. 
    destruct_a_match H;
    use_a_match_theorem_1 (equiv_sort n) H (I). 
    split; auto. apply Spec.sort_correct. apply word_order. 
    trivial. 
  Qed. 

  (** The final theorem states that:
      - the output of the circuit is never None (no failure);
      - the output of the circuit is equivalent to the output of the specification algorithm;
      - the output of the specification algorithm is sorted with respect to the particular order we chose
   *)
  
  Notation same_elements x y := (Spec.SameElements.equiv _ x y). 
  Theorem circuit_sort_correct n (I : tree (Var A) n) :
    match Circuit.output _ (csort n I) with 
      | None => False
      | Some out => exists out', (out == out' /\ Spec.tsorted n out' /\ same_elements out' I)
    end.
  Proof. 
    pose proof (circuit_sort_correct' n I).
    destruct (Circuit.output (Circuit.domain A n) (csort n I)) eqn:? . 
    + exists (sort n I). intuition.  apply Spec.SameElements.sort_equiv. 
    + auto. 
  Qed.
             
  Print Assumptions circuit_sort_correct. 
End proof.
    
(** The final circuit generator *)
Definition test size n := 
  (fun V =>
     Close V _ _ _
           (fun x =>  Circuit.rebind _ V _ (Evar x) (fun x => Circuit.sort (Tint size) V (int_cmp_swap size) n x))).

    
(** Running the circuit inside Coq, for testing purposes *)

(*  
Module sanity_check. 
  Definition c V := Circuit.sort (Tint 8) V (int_cmp_swap 8).
  Fixpoint build n i : (tree (Word.T 8) n * Z):=
    match n with 
      | 0 => (L (Word.repr 8 i), (i + 1)%Z)
      | S n => 
        let (r,i) := build n i in 
        let (l,i) := build n ((i*5+3) mod 255)%Z in 
        (N _ l r, i)
    end.
  Definition t k := c eval_type k (map (@Evar eval_type (Tint 8)) (fst (build k 0))). 
  Eval compute in Sem.eval_action (t 4) _ (Diff.init nil).
End sanity_check.
*)
Require Compiler. 

(** Exporting the circuit, for extraction *)
Definition t := (Compiler.Fesic _ _ (test 4 4)). 
  
