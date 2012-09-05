Require Import Common ZArith. 

Inductive expr := | F | T | N : positive -> expr. 

Notation var := nat. 

Definition node := (expr * var * expr)%type. 

Definition expr_eqb a b :=
  match a,b with 
    | T,T => true
    | F,F => true
    | N x, N y => (x =? y)%positive
    | _, _ => false
  end. 

Definition expr_compare x y := 
  match x,y with 
    | F , F => Eq
    | T , T => Eq
    | N x, N y => Pos.compare x y
    | F, _ =>  Lt
    | _, F => Gt
    | T, _ =>  Lt
    | _, T => Gt
  end.     

Definition node_eqb (a b: node) :=
  match a with 
    | (xa,ya,za) => 
        match b with 
          | (xb,yb,zb) => (expr_eqb xa xb && (NPeano.Nat.eqb ya yb) && expr_eqb za zb)%bool
        end
  end. 

Fixpoint assoc {A B} (eq: A -> A ->  bool) x l : option B :=
  match l with 
    | nil => None
    | cons (u,v) q => if eq x u then Some v else assoc eq x q
  end. 

Module Inner. 
  Require Import FMapPositive FMapAVL OrderedTypeAlt.
  Module PMap := PositiveMap.

  (** Rather painful proof of the fact that nodes form an ordered type *)
  Module N <: OrderedTypeAlt.
    Definition t := node.    
    Require Import Compare. 
    Definition compare (x y : t) := 
      lex  (expr_compare (snd x) (snd y)) 
           (
             (fun (x: expr * var) (y : expr * var) => 
                let (r1,v1) := x in 
                let (r2,v2) := y in 
                lex (expr_compare r1 r2) (NPeano.Nat.compare v1 v2)) (fst x) (fst y)).

        
    Lemma expr_compare_sym x y : expr_compare x y = CompOpp (expr_compare y x). 
    Proof. 
      unfold expr_compare; destruct x; destruct y; simpl; trivial.  
      apply Pos.compare_antisym. 
    Qed. 

    Lemma nat_compare_sym x y : NPeano.Nat.compare x y = CompOpp (NPeano.Nat.compare y x). 
    Proof.
      unfold NPeano.Nat.compare. 
      revert y; induction x. simpl. destruct y; reflexivity. 
      intros. simpl. destruct y. reflexivity.
      rewrite nat_compare_S. auto. 
    Qed.

    Lemma expr_compare_trans c x y z: expr_compare x y = c -> expr_compare y z = c -> expr_compare x z = c.
    Proof.  
      unfold expr_compare; destruct x; destruct y; destruct z; simpl; trivial || (try (intros; subst; discriminate)). 
      destruct c. 
      intros; rewrite Pos.compare_eq_iff in * |- *. congruence. 
      intros; rewrite Pos.compare_lt_iff in * |- *. zify.  omega.
      intros; rewrite Pos.compare_gt_iff in * |- *. zify.  omega.
    Qed.     

    (* Library issue: compare the two proofs of these lemmas... *)
    Lemma nat_compare_trans c x y z: NPeano.Nat.compare x y = c -> NPeano.Nat.compare y z = c -> NPeano.Nat.compare x z = c. 
    Proof. 
      destruct c; intros; zify. 
      intros; rewrite nat_compare_eq_iff in * |- *. congruence. 
      intros; rewrite <- nat_compare_lt in * |- *. zify.  omega.
      intros; rewrite <- nat_compare_gt in * |- *. zify.  omega.
    Qed. 

    Hint Resolve expr_compare_trans expr_compare_sym nat_compare_trans nat_compare_sym. 
    
    Lemma compare_sym x y :compare y x = CompOpp (compare x y).
    Proof. 
      intros. 
      destruct x as [[l1 v1] r1]; destruct y as [ [l2 v2] r2]; simpl. 
      apply lex_sym; eauto. 
      intros [? ?] [? ?]. apply lex_sym; eauto.  
    Qed.

    
    Lemma compare_trans c x y z : (compare x y) = c -> (compare y z) = c -> (compare x z) = c.
    Proof. 
      apply lex_trans; eauto. 
      clear. intros c [? ?] [? ?] [? ?].  apply lex_trans; eauto. 
    Qed. 
  End N.
  Module NO := OrderedType_from_Alt(N).
  

  Module NMap := FMapAVL.Make (NO).
  Notation pmap := PMap.t.
  Notation nmap := NMap.t.
  
  (** We are now ready to start speaking about BDDs  *)
  Record BDD :=
    {
      tmap : pmap node;
      hmap : nmap positive; 
      next : positive
    }. 

  Definition low b (x:expr) : option expr :=
    match x with 
      | N x => 
        match PMap.find x (tmap b) with
          | Some (y,v,z) => Some y
          | _ => None
        end
      | _ => None end.

  Definition high b (x:expr) :=
    match x with 
      | N x => 
        match PMap.find x (tmap b) with
          | Some (y,v,z) => Some y
          | _ => None
        end
      | _ => None end.


  Definition order (b: BDD) x y :=
    low b x = Some y \/ high b x = Some y. 
  
  Definition wf (b:BDD) := well_founded (order b).
  
  Definition empty :=
    {|
      tmap := PMap.empty _;
      hmap := NMap.empty _;
      next := 1
    |}.         

  Lemma wf_empty : wf empty. 
  Proof.
    intro x. apply Acc_intro. intros y o. 
    red in o; destruct o; unfold low, high, empty in H; simpl in H;
    destruct y; try rewrite PMap.gempty in H; discriminate.
  Qed.

  Definition mk_node bdd (l : expr) (v: var) (h : expr) :=
    if expr_eqb l  h then (l,bdd)
    else
      match NMap.find (l,v,h) (hmap bdd) with 
          | Some x => (N x, bdd)
          | None => let n := (l,v,h) in 
                    let u := next bdd in 
                    let bdd := {|  tmap := PMap.add u n (tmap bdd);
                                   hmap := NMap.add n u (hmap bdd);
                                   next := (u + 1)%positive |} in
                      (N u, bdd)
       end. 
  
  Section lex. 
    Context {A B: Type}. 
    Variable leA : A -> A -> Prop.
    Variable leB : B -> B -> Prop.
    Hypothesis HA : well_founded leA.
    Hypothesis HB : well_founded leB. 
    
    Inductive lex : A * B -> A * B -> Prop := 
    | left_lex :
        forall (x x' :A) (y y':B),
          leA x x' -> lex (x,y) (x',y')
    | right_lex :
        forall (x:A) (y y':B),
          leB y y' -> lex (x,y) (x,y'). 

    Lemma lex_wf : well_founded lex. 
    Proof. 
    Admitted.
  End lex. 

  Definition porder bdd : expr * expr -> expr * expr -> Prop := lex (order bdd) (order bdd).

  Section operations.

    Fixpoint eval bdd depth env (a: expr) : option bool :=
      match depth with 
        | 0 => None
        | S depth =>
          match a with 
            | T => Some true
            | F => Some false
            | N n =>    
              (        
              do x <- PMap.find n (tmap bdd);
              match x with 
                | (l,v,h) => 
                  (
                    do b <- List.nth_error env v;
                    if (b: bool) 
                    then eval bdd depth env h
                    else eval bdd depth env l)              
              end
              )
          end
      end. 

    Require Import Program.Wf.                  

    Program Fixpoint andb (bdd: BDD) (ab : expr * expr) {wf (porder bdd) ab} : option (expr * BDD) :=
      match ab with 
        | (F, _) => Some (F, bdd)
        | (_, F) => Some (F, bdd)
        | (T, x) => Some (x, bdd)
        | (x, T) => Some (x, bdd)
        | (N na, N nb) => 
          let a := N na in 
          let b := N nb in 
          do na <- PMap.find na (tmap bdd);
          do nb <- PMap.find nb (tmap bdd);
            let '(l1,v1,h1) := na in 
            let '(l2,v2,h2) := nb in 
            match NPeano.Nat.compare v1  v2 with 
              | Eq =>
                do x, bdd <- andb bdd (l1,l2);
                do y, bdd <- andb bdd (h1,h2);
                  Some (mk_node bdd x v1 y)
              | Lt =>
                  do x, bdd <- andb bdd (l1,b);
                  do y, bdd <- andb bdd (h1,b);
                  Some (mk_node bdd x v1 y)
                | _ => 
                  do x, bdd <- andb bdd (a,l2);
                  do y, bdd <- andb bdd (a,h2);
                  Some (mk_node bdd x v2 y)
                       
            end
      end.
                  Next Obligation. 
  End operations.
  
  Lemma and_correct bdd n env a b x y ab bdd' :
    eval bdd n env a = Some x ->
    eval bdd n env b = Some y ->
    andb bdd n a b = Some (ab, bdd') ->
    eval bdd' n env ab = Some (x && y)%bool.
  Proof.
     Ltac t := 
      repeat match goal with 
               | H : Some _ = Some _ |- _ => injection H; clear H; intros ?
             end.
    induction n; intros Ha Hb Hab. 
    - simpl in *.  discriminate. 
    - simpl eval in *. 
      destruct a; destruct b; simpl in Hab; t; intros; subst; f_equal.
      * auto. 
      * rewrite Bool.andb_comm. reflexivity. 
      * rewrite Bool.andb_comm. simpl.  auto. 
      * invert_do Ha; invert_do Hb. rewrite EQ, EQ1 in Hab. simpl in Hab. 
        destruct x1 as [[l1 v1] h1]. 
        destruct x0 as [[l0 v0] h0].       
        invert_do EQ0; invert_do EQ2.
        destruct x0; destruct x1. 
      auto. auto. auto.

 
invert_do Hb. rewrite EQ.  simpl. auto. 
      repeat match goal with 
          H: (do _ <- _ ; _ = Some _) |- _ => invert_do H
      end. 
      + t. exists F. simpl. exists bdd. subst. simpl. intuition. 
      + t. destruct b. 
        * t. subst. exists F. exists bdd. simpl; intuition. 
        * t. subst. exists T. exists bdd; simpl; intuition.
        *  simpl. exists (N p); exists (bdd). intuition. subst. simpl. apply Hb. 
      + destruct b;t; subst; simpl. 
        * exists F; exists bdd. intuition. destruct x; reflexivity.  
        * exists (N p); exists bdd. intuition. Require Import Bool. rewrite andb_comm. simpl. apply Ha. 
        * invert_do Ha.  invert_do Hb. rewrite EQ1, EQ.  simpl. 
          destruct x0; destruct p1; destruct x1. destruct p1.
          destruct (NPeano.Nat.compare n0 n1). 
          simpl. invert_do EQ0.  invert_do EQ2. simpl. 
          
      Ltac simpl. 
      
    Fixpoint orb depth (a b : expr) : option (expr * BDD) :=
      match depth with 
        | 0 => None
        | S depth => 
          match a,b with 
          | F, x => Some (x, bdd)
          | x, F => Some (x, bdd)
          | T, _ => Some (T, bdd)
          | _, T => Some (T, bdd)
          | N na, N nb => 
            do na <- PMap.find na (tmap bdd);
            do nb <- PMap.find nb (tmap bdd);
            match na,nb with 
              | (l1,v1,h1),(l2,v2,h2) =>
                match NPeano.Nat.compare v1  v2 with 
                  | Eq =>
                    do x, bdd <- orb depth l1 l2;
                    do y, bdd <- orb depth h1 h2;
                      Some (mk_node bdd x v1 y)
                  | Lt =>
                    do x, bdd <- orb depth l1 b;
                    do y, bdd <- orb depth h1 b;
                    Some (mk_node bdd x v1 y)
                  | _ => 
                    do x, bdd <- orb depth a l2;
                    do y, bdd <- orb depth a h2;
                    Some (mk_node bdd x v2 y)
                end
            end
          end
      end.
  
  
  
  Fixpoint negb bdd depth (a : expr) : option (expr * BDD) :=
    match depth with 
      | 0 => None
      | S depth => 
        match a with 
          | F => Some (T, bdd)
          | T => Some (F, bdd)
          | N na => 
            do na <- PMap.find na (tmap bdd);
              match na with 
                | (l,v,h) =>
                  do x, bdd <- negb bdd depth l;
                    do y, bdd <- negb bdd depth h;
                    Some (mk_node bdd x v y)
              end
        end
    end.
  
  Fixpoint xorb bdd depth (a b : expr) : option (expr * BDD) :=
    match depth with 
      | 0 => None
      | S depth => 
        match a,b with 
          | F, x => Some (x, bdd)
          | x, F => Some (x, bdd)
          | T, x => negb bdd depth x (* is this depth enough ?? *)
          | x, T => negb bdd depth x (* is this depth enough ?? *)
          | N na, N nb => 
            do na <- PMap.find na (tmap bdd);
              do nb <- PMap.find nb (tmap bdd);
              match na,nb with 
                | (l1,v1,h1),(l2,v2,h2) =>
                  match NPeano.Nat.compare v1  v2 with 
                    | Eq =>
                      do x, bdd <- xorb bdd depth l1 l2;
                        do y, bdd <- xorb bdd depth h1 h2;
                        Some (mk_node bdd x v1 y)
                    | Lt =>
                      do x, bdd <- xorb bdd depth l1 b;
                        do y, bdd <- xorb bdd depth h1 b;
                        Some (mk_node bdd x v1 y)
                    | _ => 
                      do x, bdd <- xorb bdd depth a l2;
                        do y, bdd <- xorb bdd depth a h2;
                        Some (mk_node bdd x v2 y)
                  end
              end
        end
    end.
  
  Definition var bdd x :=
    mk_node bdd F x T. 

End Inner.

Record BDD := 
  mk
    {
      content: Inner.BDD;
      depth: nat
    }.

Section t.   


Definition eval bdd env (a: expr) : option bool :=
  Inner.eval (content bdd) (depth bdd) env a. 

Definition andb bdd a b :=
  do e, r <- Inner.andb (content bdd) (depth bdd) a b;
  Some (e,mk r (depth bdd)).

Definition orb bdd a b :=
  do e, r <- Inner.orb (content bdd) (depth bdd) a b;
  Some (e,mk r (depth bdd)).

Definition negb bdd a  :=
  do e, r <- Inner.negb (content bdd) (depth bdd) a;
  Some (e, mk r (depth bdd)). 

Definition xorb bdd a b :=
  do e, r <- Inner.xorb (content bdd) (depth bdd) a b;
  Some (e,mk r (depth bdd)).

Definition ite bdd c l r:=
  do cl, bdd  <- andb bdd c l;
  do nc, bdd  <- negb bdd c;
  do ncr, bdd <- andb bdd nc r;
  orb bdd cl ncr.

Definition empty := mk Inner.empty 0.

Definition mk_var bdd x :=
  let (e, r) := Inner.var (content bdd) x in 
    (e, mk r (S (max x (depth bdd)))). 

End t. 

Definition test :=
  let bdd := empty in 
  let (a,bdd) := mk_var bdd 10 in 
  let (b,bdd) := mk_var bdd 11 in 
  do a,bdd <- orb bdd a b;
  do na,bdd <- negb bdd a;
  do r,bdd <- orb bdd a na;
  do nr,bdd <- negb bdd r;
  do nnr,bdd <- negb bdd nr;
  do x, bdd <- orb bdd nnr a;
  Some (r, bdd). 

Eval compute in test. 