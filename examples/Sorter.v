Require Import Common Core Front ZArith. 

Class order (A : Type) := 
  mk_order
    {
      le : A -> A -> bool;
      le_transitive : forall x y z, le x y = true -> le y z = true -> le x z = true;
      le_total  : forall x y , le x y = true \/ le y x = true;
      le_antisym : forall x y, le x y = true -> le y x = true -> x = y
    }.

Notation "x <= y" := (le x y).
Notation "x < y" := (negb (le y x)).

Section cmp. 
  Context {A : Type} {O : order A}.
  
  Definition min x y :=
    if x <= y then x else y. 
  Definition max x y :=
    if x <= y then y else x. 
  Definition cmp (x y: A) := (min x y, max x y).
  
  Lemma le_reflexive : forall x, x <= x = true. 
  Proof. 
    intros; destruct (le_total x x); auto. 
  Qed. 
End cmp. 
    
  

Instance bool_order : order bool. 
Proof. 
  refine (mk_order bool (fun x y => negb x || y)%bool _ _ _).
  intros [|] [|] [|]; try discriminate; reflexivity. 
  intros [|] [|]; try discriminate; auto. 
  intros [|] [|]; try discriminate; reflexivity. 
Defined. 


Section t. 
  Variable A : Type. 
  
  Inductive tree : nat -> Type :=
  | L : forall x : A, tree 0
  | N : forall n (l r : tree n), tree (S n). 

  Fixpoint reverse n t :=
    match t with 
      | L x => L x
      | N n l r => N n 
                    (reverse n r)
                    (reverse n l)
    end.

  Definition bang (l : tree 0) : A := match l with 
                                        | L x => x
                                      end. 
  
  Definition left {n} (l : tree (S n)) : tree n := match l with 
                                          | N _ l _ => l
                                        end. 
  Definition right {n} (l : tree (S n)) : tree n := match l with 
                                          | N _ _ r => r
                                        end. 

  Variable (O : order A).
  Fixpoint min_max_swap n : forall (l r : tree n), tree n * tree n :=
    match n return tree n -> tree n -> tree n * tree n with 
      | 0 => fun l r => let (x,y) := cmp (bang l) (bang r) in (L x, L y)
      | S n => fun l r => 
                let l1 := left l in 
                let r1 := right l in 
                let l2 := left r in 
                let r2 := right r in 
                let (a,b) := min_max_swap _ l1 l2 in 
                let (c,d) := min_max_swap _ r1 r2 in 
                (N _ a c, N _ b d)
    end. 

  Fixpoint merge n: tree n -> tree n := 
    match n with 
      | 0 => fun t => t
      | S k => fun t => let l := left t in 
                      let r := right t in 
                      let (a,b) := min_max_swap _ l r in
                      N _ (merge _ a) (merge _ b)
    end. 
  
  Fixpoint sort n : tree n -> tree n :=
    match n with 
      | 0 => fun t => t
      | S n => fun t => 
                let l := left t in 
                let r := right t in 
                merge (S n) (N _ (sort _ l) (reverse _ (sort _ r)))
    end. 
  
  Fixpoint list_of_tree {n} (t : tree n) :=
    match t with 
      | L x => cons x nil
      | N _ l r => List.app (list_of_tree l) (list_of_tree r)
    end. 
  
  Fixpoint tree_of_list n (l: list A) : option (tree n * list A) := 
    match n with 
      | 0 => match l with 
              | nil => None
              | cons t q => Some (L t, q)
            end
      | S n => do l, tl <- tree_of_list n l;
              do r, tl <- tree_of_list n tl;
              Some (N _ l r, tl)
    end. 

  Definition list_sort n l := 
    do t, _ <- tree_of_list n l;
    Some(list_of_tree (sort _ t)).


  Section ops. 
    
    Fixpoint Forall {n} (t : tree n) f :=
      match t with 
        | L x => f x
        | N _ l r => (Forall l f && Forall r f)%bool
      end.
  End ops.
End t.

      
Arguments Forall {A n} _ _.  
Notation "t /<= a" := (Forall  t (fun x => x <= a)) (at level 79, left associativity).
Notation "l /<=\ r" := (Forall  r (fun a => (Forall l (fun x => x <= a)))) (at level 50).

Inductive tsorted {A} {O : order A} : forall n, tree A n -> Prop :=
| tsorted_L : forall x, tsorted 0 (L _ x)
| tsorted_N : forall n l r, tsorted n l -> tsorted n r -> 
                       l /<=\ r = true -> tsorted _ (N _ _ l r).
  
Inductive bitonic_label : Type :=
| O | I | OI | IO | OIO | IOI | W.

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
  
Fixpoint label {n} (t : tree bool n) := 
  match t with
    | L x => if x then I else O
    | N  _ l r => compose (label l) (label r) 
  end. 

Definition notW l := match l with 
                       | W => false
                       | _ => true
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
    induction t2 as [ x | m s1 IH1 s2 IH2 ]. simpl. specialize (H1 _ (L _ x)); specialize (H2 _ (L _ x) ). simpl in *. rewrite H1, H2; trivial. 
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
  
  exfalso; apply tree_le_OI in H5 ;[congruence | auto].
  exfalso; apply tree_le_OI in H5 ;[congruence | auto].
  exfalso; apply tree_le_OI in H5 ;[congruence | auto].
  exfalso; apply tree_le_OI in H5 ;[congruence | auto].
Qed. 


Definition label_opp l :=
  match l with 
    | IO => OI | OI => IO | l => l
  end. 

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
         end; try congruence. 
     
     rewrite label_reverse, ? label_opp_move; simpl; auto. 
     rewrite label_reverse, ? label_opp_move; simpl; auto. 
     rewrite label_reverse, ? label_opp_move; simpl; auto. 
     rewrite label_reverse, ? label_opp_move; simpl; auto. 
Qed. 

Definition bitonic {n} (t : tree bool n) := 
  match label t with 
    | W => false
    | _ => true
  end. 

Lemma sorted_sorted_down_bitonic n (t1 t2 : tree bool n) : 
  tsorted n t1 -> tsorted n (reverse _ _ t2) -> 
  bitonic (N _ _ t1 t2) = true. 
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
  (* Some proofs about the min_max_swap function *)
  
  
  Lemma tree_O_inversion : forall t : tree bool 0, exists x, t = L _ x. 
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
      bitonic (N _ n  l r) = true -> 
      let (a,b) := (min_max_swap  _ l r) in 
      bitonic a = true /\
      bitonic b = true /\
      a /<=\ b = true. 
    Proof. 
      induction n. 
      - unfold bitonic; simpl.
        dependent destruction l; dependent destruction r; destruct x; destruct x0; simpl; 
        try discriminate; compute; intuition. 
      - unfold bitonic.  replace (label (N bool (S n) l r)) with (compose (label l) (label r)) by reflexivity;
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

      Lemma tree_le_N_left n t1 t2 : forall  m (t: tree bool m), 
        N _ n t1 t2 /<=\ t = true -> 
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
        t1 /<=\ t = true -> t2 /<=\ t = true ->         N _ n t1 t2 /<=\ t = true.
      Proof.
        induction m. 
        - intros; init; simpl in *; apply Bool.andb_true_iff; intuition. 
        - intros. dependent destruction t.  simpl in *. 
          rewrite ? Bool.andb_true_iff in *. 
          intuition. 
      Qed. 
        
      Hint Resolve tree_le_N_left' .
      
      Lemma tree_le_N_right n t1 t2 m (t: tree bool m): 
        t /<=\ N _ n t1 t2 = true -> 
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
            t /<=\ N _ n t1 t2 = true.
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
          set (l := left _ t1). set (r := right _ t1). 
          assert (t1 = N _ _ l r). dependent destruction t1; reflexivity. 
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
          set (l := left _ t1). set (r := right _ t1). 
          assert (t1 = N _ _ l r). dependent destruction t1; reflexivity. 
          rewrite H0 in H. apply tree_le_N_right in H.  destruct H. 
          pose proof (tree_le_min_max_swap_right _ _ _ _ _ H H1). 
          destruct (min_max_swap _ l r) as [a b] eqn:Hab. 
          intuition. 
      Qed. 
                                
    End misc. 

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

    Lemma sort_tsorted : forall n t , tsorted _ (sort _ _  n t). 
    Proof. 
      induction n. 
      - intros. simpl. dependent destruction t.  apply tsorted_L. 
      - dependent destruction t. simpl. 
        set (l :=  (sort bool _ n t1)). 
        set (r :=  (sort bool _  n t2)). 
        destruct (min_max_swap n l (reverse bool n r)) as [a b] eqn: Hab. 
        assert (bitonic (N bool n l (reverse bool n r))= true). 
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

(* Same predicate as [tsorted] but on lists *)
Inductive sorted {A} {O : order A} : list A -> Prop :=
| sorted_nil : sorted nil
| sorted_cons : forall t q, sorted q -> List.Forall (fun x => t <= x = true) q -> sorted (t::q).

Fixpoint map {A B n} (f :A -> B) : tree A n -> tree B n :=
  match n with 
    | 0 => fun t => let x := bang A t in L _ (f x)
    | S n => fun t => N _ _ (map f (left _ t)) (map f (right _ t))
  end. 

Definition monotone {A B} (PA : order A) (PB : order B) (f : A -> B) :=
  (forall( a b : A), le a b = true -> le (f a) (f b) = true).

Module zero_one_principle. 
  Section inner. 
  Require Import Morphisms. 

  Coercion is_true (b : bool) : Prop := b = true. 
                
  Variable sort : forall A, order A -> forall n, tree A n -> tree A n.
  Hypothesis H : forall n (t : tree bool n), tsorted n (sort _ bool_order n t).

  
  Hypothesis Hcommute : forall {A B} {PA : order A} {PB : order B} (f : A -> B) 
                                     (Hf : monotone PA PB f), 
    forall n t,
      map f (sort A PA n t)  = sort B PB n (map f t). 


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

  Lemma not_sorted_app : forall l1 l2, ~ sorted l2 ->  ~ sorted (List.app l1 l2).
  Proof. 
    induction l1. simpl. tauto. 
    simpl. intros l2 Hl2 Hf.  
    inversion Hf. subst.
    apply (IHl1 l2 Hl2 H2). 
  Qed. 

  Lemma tsorted_sorted_list_of_tree A (R: order A): forall n (t : tree A n ), tsorted n t <-> sorted (list_of_tree A t). 
  Proof. 
    induction n. 
    - dependent destruction t.  simpl. intuition. constructor. constructor.  auto. inversion H0. subst. constructor. 
    - dependent destruction t. split; intros. 
      inversion H0; injectT. 
      simpl.
      Lemma sorted_app A (R : order A):
        forall l1 l2, sorted l1 -> sorted l2 ->
                 List.Forall (fun x => List.Forall (fun y => y <= x = true) l1) l2 -> 
                 sorted (l1 ++ l2). 
      Admitted. 
      apply sorted_app. rewrite <- IHn.  auto. rewrite <- IHn. auto. 
      clear - H6. 
      admit.
      constructor. 
      rewrite IHn. simpl in H0. 
  Admitted. 
  
  Theorem zero_one_principle :
    forall A (R : order A) n t, tsorted n (sort A R  n t) .
  Proof.
    Require Import Classical.
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

    rewrite tsorted_sorted_list_of_tree in H1. 
    
    
    apply not_sorted_inversion in H1. 
    destruct H1 as [l1 [x [y [ l2 [H1 H2] ]]]].
    set (f := fun (c : A) => if c < x then false else true).
    set (b := sort A R n t) in *. 
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
      clear - H6 H2 f.  
    
      assert (monotone _ _ f). 
      {
        unfold monotone. clear - f. intros. unfold f.  
        destruct  (le x a) eqn : Ha; 
          destruct  (le x b) eqn : Hb; trivial.
        exfalso. 
        pose proof (le_transitive _ _ _ Ha H). congruence. 
      }
      assert (Hx : f x = true ). unfold f.  rewrite le_reflexive. reflexivity. 
      assert (Hy : f y = false). unfold f. rewrite H2. reflexivity. 
      rewrite Hx, Hy in H6. simpl in H6. discriminate. 
    }      
    apply H0.  unfold b. 

    rewrite (Hcommute A bool _ bool_order). apply H. 
    {
      unfold monotone. clear - f. intros. unfold f.  
      destruct  (le x a) eqn : Ha; 
        destruct  (le x b) eqn : Hb; trivial.
      exfalso. 
      pose proof (le_transitive _ _ _ Ha H). congruence. 
    }
  Qed. 
  
  Print Assumptions zero_one_principle. 
  End inner. 
End zero_one_principle.   

Fixpoint pow2 n :=
  match n with 
    | 0 => 1
    | S n => let x := pow2 n in x + x
  end. 

Lemma tree_of_list_2n_gen : forall A n l, (pow2 n <= List.length l)%nat  -> 
                                 {t | tree_of_list A n l = Some (t, List.skipn (pow2 n) l)}. 
Proof. 
  induction n. 
  -  simpl. destruct l. simpl; intros; omega. 
  intros. exists (L _ a). reflexivity. 
  -   intros. simpl in H. 
      set (l1 := List.firstn (pow2 n) l). 
      set (l2 := List.skipn (pow2 n) l). 
      destruct (IHn l) as [t1 H1].  zify. omega. 
      destruct (IHn (List.skipn (pow2 n) l)) as [t2 H2]. 
      {
        Lemma skipn_length : forall A n (l: list A), List.length (List.skipn n l) = List.length l - n. 
        Proof. 
         induction n. 
         - simpl. intros. omega. 
         - intros l.  simpl. destruct l. reflexivity. 
           simpl. auto.  
        Qed. 
        rewrite skipn_length.  zify; omega. 
      }
      exists (N _ _ t1 t2). simpl. rewrite H1. simpl. rewrite H2. simpl. 
      f_equal. f_equal. 
      
      Lemma skipn_plus A n : forall m (l : list A), List.skipn m (List.skipn n l) = List.skipn (n + m) l. 
      Proof. 
        induction n. simpl. reflexivity.
        simpl. 
        intros. destruct l. destruct m; reflexivity. 
        auto. 
      Qed. 
      apply skipn_plus. 
Qed. 

Lemma tree_of_list_2n : forall A n l, List.length l = pow2 n -> 
                                 {t | tree_of_list A n l = Some (t, nil)}. 
Proof. 
  intros. 
  destruct (tree_of_list_2n_gen A n l) as [t Ht]. zify; omega. 
  exists t. rewrite Ht. f_equal. f_equal. 
  assert   (List.length (List.skipn (pow2 n) l) = 0).  rewrite skipn_length. rewrite H; zify; omega. 
  revert H0. clear. generalize (List.skipn (pow2 n) l). destruct l0; try discriminate. reflexivity. 
Qed. 
  
 
  

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

    
  Lemma min_commute : forall (x y: A), f (min x y) = min (f x) (f y). 
  Proof. 
  Admitted. 

  Lemma max_commute : forall (x y: A), f (max x y) = max (f x) (f y). 
  Proof. 
  Admitted. 
  
  Lemma min_max_swap_commute :
    forall (n : nat) (t1 t2 : tree A n) ,
      (let (a,b) := (min_max_swap A PA n t1 t2) in 
       (map f a, map f b)) = min_max_swap B PB n (map f t1) (map f t2). 
  Proof. 
    induction n; dependent destruction t1; dependent destruction t2. 
    simpl. 
    
    {
      rewrite min_commute, max_commute. reflexivity. 
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
  }
Qed. 

Print Assumptions sort_correct. 
      
Module Circuit. 
  Section t. 
  Require Import Front.
  
  Variable A : type.
  Variable Var : type -> Type. 

  Notation T n := (tree (Var A) n). 
  Notation "x ⊗ y" := (Ttuple [x;y]) (at level 74). 
  
  Fixpoint domain n := 
    match n with 
      | 0 => A
      | S n => (domain n) ⊗ (domain n)
    end. 
    
  Definition C n := action nil Var (domain n). 
  
  Fixpoint reverse n (t : T n) : C n  :=
    match t with 
      | L x => Return (Evar x)
      | N n l r => 
        do r <- reverse n r;
        do l <- reverse n l;
        ret [tuple r, l]
    end%action.

  Definition bang (l : T 0) : Var A := match l with
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
  
  Variable cmp : Var A -> Var A -> action nil Var (Ttuple [A ; A]). 
  
  Notation mk_N x y := ([tuple x,y])%expr.
  Fixpoint min_max_swap n : forall (l r : T n), C (S n) :=
    match n return T n -> T n -> action nil Var ((domain n) ⊗ (domain n)) with 
      | 0 => fun l r => cmp (bang l) (bang r)
      | S n => fun l r => 
                let l1 := left l in 
                let r1 := right l in 
                let l2 := left r in 
                let r2 := right r in 
                do x <- min_max_swap _ l1 l2;
                do (a,b) <~ x; 
                do y <- min_max_swap _ r1 r2; 
                do (c,d) <~ y;
                ret ([tuple mk_N a c, mk_N b d])
    end%action. 

  (*  The classic bind  *)
  Notation "'do' x <~ a ; b " := (Bind a (fun x =>  b)) 
                                (at level 200, x ident, a at level 100, b at level 200) 
                                 : action_scope. 

  Fixpoint rebind {U} n : Var (domain n) -> (T n -> action nil Var U) -> action nil Var U :=
    match n with 
      | 0 => fun t f => f (L _ t)
      | S n => fun t f => 
                do (a,b) <~ Evar t;
                do a <~ ret a;
                do b <~ ret b;
                rebind _ a (fun t1 => 
                              rebind _ b (fun t2 => 
                                            f (N _ _ t1 t2)
                                         )
                           )
    end%action. 

  Notation "'do' x <: a ; b" :=  
    (do foo <~ ret a; 
     rebind _ foo (fun x =>  b))%action 
      (at level 200, x ident, a at level 100, b at level 200) 
    : action_scope. 

    
  
  Fixpoint merge n: T n -> C n := 
    match n with 
      | 0 => fun t => ret (Evar (bang t))
      | S k => fun t => 
                let l := left t in
                let r := right t in
                do x <-  min_max_swap _ l r;
                do (a,b) <~ x;
                do a <: a;      (* use an explicit reification step *)
                do b <: b;      (* use an explicit reification step *)
                do a <- merge _ a;
                do b <- merge _ b;
                ret (mk_N  a b)
    end%action. 
  
  
  Fixpoint sort n : T n -> C n :=
    match n with 
      | 0 => fun t => ret (Evar (bang t))
      | S n => fun t => 
                let l := left t in 
                let r := right t in 
                do l <- sort _ l; 
                do r <- sort _ r; do r <: r;
                do r <- reverse _ r;                 
                do x <- ret (mk_N l r);
                do x <~ ret x;
                rebind (S n) x (fun x => merge _ x)
    end%action. 
  End t.

  Definition output  (t : type) (A : Action nil t) : 
    option (eval_type t) :=    
    match Front.Eval [] DList.DList.nil t A (Diff.init []%list)  with
      | Some p => Some (fst p)
      | None => None
    end. 

  Section proof. 
    (*  *)
    Variable A : type. 

    Notation Var := eval_type.
    Variable cmp : Var A -> Var A -> action nil Var (Ttuple [A ; A]). 
    Inductive csorted : forall n, eval_type (domain A n) -> Prop :=
    | csorted_0 : forall x, csorted 0 x
    | csorted_S : forall n (l r : eval_type (domain A n)), 
                    csorted n l -> 
                    csorted n r -> 
                    csorted (S n) (l, (r, tt))%expr.

    
    Theorem correction n input  : 
      match output _ (sort A Var cmp n input) with 
        | None => False          (* this means that we always get an answer *)
        | Some o => csorted n (o)
      end. 
    
End Circuit.


Definition int_cmp_swap {Var : type -> Type} n := 
  fun (x y : Var (Tint n)) => 
    let x := Evar x in let y := Evar y in 
    (do c <- ret (x < y)%expr;
     do min <- ret (Emux c x y)%expr;
     do max <- ret (Emux c y x)%expr;
     @Return nil _ _  [tuple min, max]
    )%action. 
    
                                                   

Section close. 
  
  Variable Var : type -> Type.

  Notation "'do' x <~ a ; b " := (Bind a (fun x =>  b)) 
                                   (at level 200, x ident, a at level 100, b at level 200) 
                                 : action_scope. 
  
  Definition primitive_generalize args res l1 (p : primitive l1 args res) l2:
    primitive (List.app  l1 l2) args res :=
    match p with
      | input_read t x => input_read _ _  (var_lift x )
      | register_read t x => register_read (var_lift x)
      | register_write t x => register_write (var_lift x)
      | regfile_read n t v => regfile_read  (var_lift v)
      | regfile_write n t v => regfile_write (var_lift v)
    end.
      
  Definition generalize (l1 : list sync) T (a : action l1 Var T) : forall l2, action (List.app l1 l2) Var T. 
  refine (let fix aux (l1 : list sync) T (a : action l1 Var T) :
                  forall l2, action (List.app l1 l2) Var T :=
                match a  with
                  | Return t exp => fun l2 => Return (exp)
                  | Bind t u a f => fun l2 => let a' := aux _ _ a l2 in Bind a' (fun x => aux _ _ (f x) _)
                  | Assert e => fun l2 => Assert e
                  | Primitive args res p exprs => fun l2 : list sync =>
                                                   Primitive args res 
                                                             (primitive_generalize args res _ p l2)
                                                             exprs
                  | OrElse t b1 b2 => fun l2 => OrElse _ _ t (aux _ _ b1 l2) (aux _ _ b2 l2)
                end
            in aux l1 T a
           ).
  Defined. 

  Fixpoint var_last {A} (l : list A) (t : A) : var (List.app l [t]) t :=
    match l with 
      | nil => var_0
      | hd :: q => var_S (var_last q t)
      end%list. 
  
  Definition internalize {Phi T U} (c : Var T -> action Phi Var U) : 
    action (List.app Phi [Tinput T]) Var U :=
    let v := (var_last Phi (Tinput T)) in 
    (do x <~ Primitive nil T  (input_read (List.app Phi [Tinput T]) T  v) DList.DList.nil; 
      generalize _ _ (c x) _)%action.
  
End close.
  
Definition test size n := 
  (fun V =>
     internalize _
       (fun x => Circuit.rebind _ V _ x (fun x => Circuit.sort (Tint size) V (int_cmp_swap size) n x))).

Module sanity_check. 
  Definition c V := Circuit.sort (Tint 8) V (int_cmp_swap 8).
  Fixpoint build n i : (tree (Word.T 8) n * Z):=
    match n with 
      | 0 => (L _ (Word.repr 8 i), (i + 1)%Z)
      | S n => 
        let (r,i) := build n i in 
        let (l,i) := build n ((i*5+3) mod 255)%Z in 
        (N _ _ l r, i)
    end.
  Definition t k := c eval_type k (fst (build k 0)). 
  (* Arguments N {A n} _ _.  *)
  (* Eval compute in fst (build 4 0). *)
  Eval compute in Sem.eval_action (t 4) _ (Diff.init nil).
End sanity_check.
Require Compiler. 
Definition t := (Compiler.fesiopt _ _ (test 4 4)). 
  
