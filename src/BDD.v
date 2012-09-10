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
  Require FMapFacts. 
  Module PMap := PositiveMap.
  Module PMapFacts := FMapFacts.Facts(PMap).

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
  Module NMapFacts := FMapFacts.Facts (NMap). 

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
          | Some (y,v,z) => Some z
          | _ => None
        end
      | _ => None end.


  Definition order (b: BDD) x y : Type :=
    ((low b x = Some y) + (high b x = Some y))%type. 
  
  
  Definition empty :=
    {|
      tmap := PMap.empty _;
      hmap := NMap.empty _;
      next := 1
    |}.         

  Definition upd b u :=
    {| 
      tmap := PMap.add (next b) u (tmap b);
      hmap := NMap.add u (next b) (hmap b);
      next := (1 + next b)
    |}. 

  Definition mk_node bdd (l : expr) (v: var) (h : expr) :=
    if expr_eqb l  h then (l,bdd)
    else
      match NMap.find (l,v,h) (hmap bdd) with 
          | Some x => (N x, bdd)
          | None => let n := (l,v,h) in 
                    let u := next bdd in 
                    (N u, upd bdd n)
       end. 
  
  Section t. 
    Variable env: nat -> bool. 
    Section operations.
      Fixpoint interp bdd depth (a : expr) : option bool :=
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
                      ( if env v
                        then interp bdd depth h
                        else interp bdd depth l)              
                  end
                )
            end
        end. 
      
      Fixpoint andb (bdd: BDD) depth (a b : expr)  : option (expr * BDD) :=
        match depth with 
          | 0 => None 
          | S depth => 
            match a,b with 
              | F, _ => Some (F, bdd)
              | _, F => Some (F, bdd)
              | T, x => Some (x, bdd)
              | x, T => Some (x, bdd)
              | N na, N nb => 
                let a := N na in 
                let b := N nb in 
                do na <- PMap.find na (tmap bdd);
                do nb <- PMap.find nb (tmap bdd);
                let '(l1,v1,h1) := na in 
                let '(l2,v2,h2) := nb in 
                match NPeano.Nat.compare v1  v2 with 
                  | Eq =>
                    do x, bdd <- andb bdd depth l1 l2;
                    do y, bdd <- andb bdd depth h1 h2;
                    Some (mk_node bdd x v1 y)
                  | Lt =>
                    do x, bdd <- andb bdd depth l1 b;
                    do y, bdd <- andb bdd depth h1 b;
                    Some (mk_node bdd x v1 y)
                  | _ => 
                    do x, bdd <- andb bdd depth a l2;
                    do y, bdd <- andb bdd depth a h2;
                    Some (mk_node bdd x v2 y)
                end                       
            end
        end.
      
      Fixpoint orb bdd depth (a b : expr) : option (expr * BDD) :=
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
                          do x, bdd <- orb bdd depth l1 l2;
                            do y, bdd <- orb bdd depth h1 h2;
                            Some (mk_node bdd x v1 y)
                        | Lt =>
                          do x, bdd <- orb bdd depth l1 b;
                            do y, bdd <- orb bdd depth h1 b;
                            Some (mk_node bdd x v1 y)
                        | _ => 
                          do x, bdd <- orb bdd depth a l2;
                            do y, bdd <- orb bdd depth a h2;
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
      
      Definition mk_var bdd x :=
        mk_node bdd F x T. 
    End operations.
    
    Inductive value bdd : expr -> bool -> Type :=
    | value_F : value bdd F false
    | value_T : value bdd T true
    | value_N : forall p l v h, 
                  PMap.find p (tmap bdd) = Some (l,v,h) -> 
                  forall vl, value bdd l vl -> 
                  forall vh, value bdd h vh -> 
                        value bdd (N p) (if env v then vh else vl).    
    
    
    Lemma value_T_inversion bdd v : value bdd T v -> v = true. 
    Proof. 
      intros H; inversion H; intuition. 
    Qed. 
    
    Lemma value_F_inversion bdd v : value bdd F v -> v = false. 
    Proof. 
      intros H; inversion H; intuition. 
    Qed. 
    
    Lemma value_N_inversion bdd a va : value bdd (N a) va -> 
                                       forall l x h, PMap.find a (tmap bdd) = Some (l, x, h) -> 
                                       { vl : bool & 
                                       {vh : bool & 
                                                  (value bdd l vl * 
                                                   value bdd h vh * 
                                                   value bdd (N a) (if env x then vh else vl))%type }}. 
    Proof. 
      intros. inversion H. subst.
      exists vl.  exists vh. intuition; try  congruence. 
      assert (x = v) by congruence. subst.  congruence. 
    Qed. 
    
    Lemma value_inj bdd x v1:
      value bdd x v1 -> 
      forall v2, value bdd x v2 -> 
            v1 = v2. 
    Proof. 
      induction 1. 
      intros. apply value_F_inversion in H;congruence. 
      intros. apply value_T_inversion in H;congruence. 
      intros v2 Hv2. 
      inversion Hv2; subst. 
      rewrite e in H2. injection H2; intros; clear e H2; subst. 
      specialize (IHvalue1 _ H3). 
      specialize (IHvalue2 _ H4). subst. 
      reflexivity. 
    Qed. 
  End t. 

  Record wf (env : nat -> bool) (b: BDD) : Type :=
    {
      wf_bijection : forall p n, NMap.find n (hmap b) = Some p 
                            <-> PMap.find p (tmap b) = Some n;
      wf_lt_next : forall p x, PMap.find p (tmap b) = Some x -> 
                          (p < next b)%positive;
      wf_depth : nat;
      wf_value_interp: forall x vx, value env b x vx -> 
                               interp env b wf_depth x = Some vx;
      wf_value_order x vx : value env b x vx -> 
                            forall y, order b x y ->
                                 {vy : bool & value env b y vy};
      wf_find_value : forall p x, PMap.find p (tmap b) = Some x -> 
                             {vp : bool & value env b (N p) vp}
                               
    }.
     
  Hint Constructors value. 
  Hint Resolve value_inj. 
  
   
  Lemma pmap_order_left {b} {x l v h}: 
    PMap.find x (tmap b) = Some (l, v, h) -> 
    order b (N x) l. 
  Proof. 
    intros H; left; simpl; rewrite H. reflexivity. 
  Qed. 
  
  Lemma pmap_order_right {b} {x l v h}: 
    PMap.find x (tmap b) = Some (l, v, h) -> 
    order b (N x) h. 
  Proof. 
    intros H; right; simpl; rewrite H. reflexivity. 
  Qed. 
  
  Hint Resolve pmap_order_left pmap_order_right. 
  
  Record incr env (b1 b2 : BDD) :=
    {
      incr_order : forall x y, order b1 x y -> order b2 x y;
      incr_value : forall x v, value env b1 x v -> 
                              value env b2 x v;
      incr_wf : wf env b1 -> wf env b2 
    }.
  
  Hint Resolve incr_value incr_order incr_wf. 
  
  Remark bind2_inversion:
    forall {A B C: Type} (f: option (A*B)) (g: A -> B -> option C) (y: C),
      bind2 f g = Some y ->
      {x1 : A & {x2 : B | f = Some (x1,x2) /\ g x1 x2 = Some y}}.
  Proof. 
    intros ? ? ? [ [x y] | ] ? ? H; simpl in H; eauto.
    discriminate. 
  Qed.
  
  Lemma incr_refl env bdd : incr env bdd bdd. 
  Proof. 
    constructor; tauto. 
  Qed. 
  
  Lemma incr_trans env a b c : incr env a b -> incr env b c -> incr env a c. 
  Proof. 
    intros Hab Hbc. 
    constructor; 
      intros; apply Hbc; apply Hab; auto.   
  Qed. 
  
  Hint Resolve incr_trans incr_refl. 
  
  
  Lemma interp_S n: 
    forall {env bdd p x}, 
      interp env bdd n p = Some x ->
      interp env bdd (S n) p = Some x.
  Proof.
    induction n. 
    - discriminate. 
    - intros. 
      simpl in H. 
      destruct p; simpl; try tauto.
      
      Ltac t := 
        repeat 
          match goal with 
            | H : Some _ = Some _ |- _ => injection H; clear H; intros ?
            | H : (None = Some _) |- _ => discriminate
            | H : (bind ?F ?G = Some ?X) |- _ => 
              destruct (bind_inversion _ _ F G _ H) as [?x [?h ?h]]; clear H
            | H : (bind2 ?F ?G = Some ?X) |- _ => 
              destruct (bind2_inversion F G _ H) as [?x [?x [?h ?h]]]; clear H
            | |- context [(bind (Some _) ?G)] => simpl
            | H : (bind ?x ?f = None) |- _ => 
              destruct (bind_inversion_None x f H) as [?h | [?x [?h ?h]]]
            | H : ?x = Some ?y |- context [?x] => rewrite H
          end. 
      t. 
      destruct x0 as [[l1 v1] h1].
      destruct (env v1);
      apply IHn in h0; assumption. 
  Qed.       

  Hint Resolve interp_S. 
  
  Lemma value_upd  env bdd (Hwf: wf env bdd) l v h:
    NMap.find (l,v,h) (hmap bdd) = None ->
    forall vl, value env bdd l vl -> 
          forall vh, value env bdd h vh -> 
                forall x vx, value env bdd x vx -> 
                        value env (upd bdd (l,v,h)) x vx. 
  Proof.              
    intros Hbdd vl Hvl vh Hvh x vx H.
    induction H. 
    constructor. 
    constructor. 
    econstructor; eauto. 
    simpl. rewrite PMap.gso. auto. 
    destruct Hwf as [ _ Hwf]. apply Hwf in e. clear - e. zify; omega. 
  Qed. 
  Hint Resolve value_upd.   
  
  Lemma expr_eq_dec (e1 e2: expr) : ({e1 = e2} + {e1 <> e2})%type.  
  Proof.
    decide equality. 
    apply Pos.eq_dec. 
  Qed. 
  
  Lemma node_eq_dec (n1 n2: node) : {n1 = n2} + {n1 <> n2}.  
  Proof. 
    decide equality. 
    apply expr_eq_dec. 
    decide equality. 
    apply NPeano.Nat.eq_dec.  
    apply expr_eq_dec. 
  Qed. 
  
  Lemma expr_compare_refl e : expr_compare e e = Eq.  
  Proof.
    destruct e; trivial.
    simpl. 
    apply Pos.compare_refl. 
  Qed. 
  
  Lemma node_compare_refl n : N.compare n n = Eq.  
  Proof.
    clear. 
    destruct n as [[e1 v] e2]. unfold N.compare. 
    rewrite expr_compare_refl; simpl. 
    rewrite expr_compare_refl; simpl. 
    rewrite nat_compare_eq_iff. reflexivity. 
  Qed.
  
  Lemma node_compare_eq_iff n1 n2 : N.compare n1 n2 = Eq <-> n1 = n2. 
  Proof. 
    clear; split; intros. 
    
    2:subst; apply node_compare_refl. 
    unfold N.compare in H. 
    destruct (expr_compare (snd n1) (snd n2)) eqn:H3; try discriminate. 
    destruct n1 as [[a b] c]; destruct n2 as [[a' b'] c']. simpl in H. 
    destruct (expr_compare a a') eqn: H1; try discriminate. 
    rewrite nat_compare_eq_iff in H. subst. 
    simpl in H3. 
    Lemma expr_compare_eq a b: expr_compare a b = Eq -> a = b.  
    Proof. 
      destruct a ; destruct b; simpl; intros; subst;  try discriminate; try reflexivity.  
      rewrite Pos.compare_eq_iff in H. subst. auto. 
    Qed. 
    apply expr_compare_eq in H1. apply expr_compare_eq in H3. subst; reflexivity.
  Qed. 

  Remark wf_neq env bdd (Hwf : wf env bdd) p x : PMap.find p (tmap bdd) = Some x -> p <> next bdd. 
  Proof. 
    intros H. apply (wf_lt_next _ _ Hwf) in H; auto.  zify; omega. 
  Qed. 
  Hint Resolve wf_neq. 
    

  Section wf_upd.  
    Variable env : nat -> bool. 
    Variable bdd : BDD. 
    Hypothesis Hwf : wf env bdd.
    Variable (l:expr) (v:nat) (h:expr). 
    Variable vl vh : bool. 
    Hypothesis Hvl : value env bdd l vl. 
    Hypothesis Hvh : value env bdd h vh. 
    Hypothesis Hnode : NMap.find (elt:=positive) (l, v, h) (hmap bdd) = None.

    Remark value_upd_left : value env (upd bdd (l,v,h)) l vl. 
    Proof. 
      eapply value_upd; eauto. 
    Qed. 
    Remark value_upd_right : value env (upd bdd (l,v,h)) h vh. 
    Proof. 
      eapply value_upd; eauto. 
    Qed. 
    
    Lemma order_upd : forall x y : expr, order bdd x y -> order (upd bdd (l, v, h)) x y.
    Proof. 
      intros x y [Hxy | Hxy]; [left | right].
      + unfold low in *; destruct x; auto. 
        case_eq (PMap.find p (tmap bdd)); [intros [[l1 v1] h1] H| intros H].
        *  simpl; rewrite H in Hxy.
           rewrite PMap.gso by eauto. setoid_rewrite H; assumption.
        *  rewrite H in Hxy. discriminate.
      +  unfold high in *; destruct x; auto.
         case_eq (PMap.find p (tmap bdd)); [intros [[l1 v1] h1] H| intros H].
         *  simpl; rewrite H in Hxy.
            rewrite PMap.gso by eauto. setoid_rewrite H; assumption.
         * rewrite H in Hxy. discriminate.
    Qed.  
           
    Lemma value_upd_inj x vx vy : value env bdd x vx -> 
                          value env (upd bdd (l,v,h)) x vy -> 
                          vx = vy. 
    Proof.
      intros. 
      eapply value_upd in H; eauto. 
    Qed. 
      
    Lemma interp_upd : forall (n : var) (x : expr) (y : bool),
                         interp env bdd n x = Some y -> interp env (upd bdd (l, v, h)) n x = Some y.
    Proof.
      induction n; intros. discriminate.
      simpl in *.
      destruct x; intuition.
      t; destruct x as [[l2 v2] h2]; t.
      
      rewrite PMap.gso by eauto. setoid_rewrite h0; simpl.
      destruct (env v2) eqn: Heq;t; intuition.
    Qed.
      
    Lemma wf_value_lt x vx : value env bdd (N x) vx -> 
                             (x < next bdd)%positive. 
    Proof.
      clear - Hwf. 
      intros H. inversion H.  subst.
      destruct Hwf; eauto. 
    Qed. 
    
    Hint Resolve wf_value_lt wf_value_order.

    Lemma value_upd_neq x vx :  value env (upd bdd (l, v, h)) x vx ->
                                N (next bdd) <> x ->
                                value env bdd x vx.
    Proof.
      intros. 
      induction H;  auto. 
      simpl in e. rewrite PMap.gso in e by congruence. 
      destruct (wf_find_value _ _ Hwf  _ _ e) as [vp Hvp]. 

      refine (let IH1 := IHvalue1 _ in 
              let IH2 := IHvalue2 _ in _). 
      destruct l0 as [ | | X ]; try discriminate;  
      assert (HX : (X < next bdd)%positive) by
          (refine (let H := wf_value_order _ _ Hwf _ _ Hvp  (N X) _ in 
                   let (x, Hx) := H in wf_value_lt _ _ Hx 
                 ); [eauto ]). 
      clear - HX. intros H; injection H; clear H. zify; omega. 
      destruct h0 as [ | | X ]; try discriminate;  
      assert (HX : (X < next bdd)%positive) by
          (refine (let H := wf_value_order _ _ Hwf _ _ Hvp  (N X) _ in 
                   let (x, Hx) := H in wf_value_lt _ _ Hx 
                 ); [eauto ]). 
      clear - HX. intros H; injection H; clear H; intros. zify; omega. 
      econstructor; eauto. 
    Qed.

    
    (* Lemma value_upd_eq x vx : value env (upd bdd (l,v,h)) x vx -> *)
    (*                           x = N (next bdd) ->  *)
    (*                           value env (upd bdd (l,v,h)) x (if env v then vh else vl).  *)
    
    Lemma order_upd_eq x y : order (upd bdd (l,v,h)) x y -> 
                             x = N (next bdd) -> 
                             forall vx, value env (upd bdd (l,v,h)) x vx ->
                                   (y = l) + (y = h). 
    Proof. 
      intros H H' vx Hvx. subst. 
      destruct H as [H | H];  
        simpl in H; inversion Hvx; subst;
        simpl in H1; rewrite H1 in H; injection H; intros; subst; clear H; 
        rewrite PMap.gss in H1 by eauto.
      left; congruence. 
      right; congruence. 
    Qed. 
    
    Lemma order_upd_neq x y : order (upd bdd (l,v,h)) x y -> 
                              x <> N (next bdd) -> 
                              forall vx, value env (upd bdd (l,v,h)) x vx ->
                                    order bdd x y. 
    Proof. 
      intros H H' vx Hvx.
      destruct x as [ | | x]. 
      destruct H as [ H | H]; simpl in H; discriminate. 
      destruct H as [ H | H]; simpl in H; discriminate. 
      destruct H as [ H | H]; simpl in H; rewrite PMap.gso in H by (clear - H'; congruence). 
      left; apply H. 
      right; apply H. 
    Qed. 
    
    Lemma wf_upd : wf env (upd bdd (l, v, h)).
    Proof. 
      
      refine ((fun wf_equiv wf_lt_next wf_depth wf_value_interp wf_value_order wf_find_value =>
                Build_wf env _
                         wf_equiv wf_lt_next wf_depth 
                         wf_value_interp 
                         (wf_value_order (* wf_find_value env wf_value_interp *))
                         wf_find_value
              ) _ _ (1 + wf_depth env _ Hwf) _ _  _). 

      - clear Hvl Hvh. revert Hnode.   generalize (l,v,h) as n1; intros n1 Hn1 p n2. 
        simpl. 
        destruct (node_eq_dec n1 n2) as [Hn | Hn]; [subst|].
        + rewrite NMapFacts.add_eq_o. 
          split; intros H.
          * injection H; clear H; intros; subst.  
            rewrite PMap.gss. reflexivity. 
          * f_equal. 
            destruct (Pos.eq_dec (next bdd) p); [trivial|]. 
            exfalso. 
            rewrite PMap.gso in H by congruence. 
            rewrite <- (wf_bijection _ _ Hwf) in H; congruence. 
          * apply node_compare_refl. 
            
        + rewrite NMapFacts.add_neq_o by (rewrite node_compare_eq_iff; tauto).
          split; intros. 
          rewrite (wf_bijection _ _ Hwf) in H. 
          rewrite PMap.gso; eauto. 
          rewrite PMap.gso in H. 
          destruct Hwf as [ H' H'' _ _ ].
          rewrite H'. auto.
          intros Hp. subst. 
          rewrite PMap.gss in H. congruence. 
      - intros. simpl in H. 
        destruct (Pos.eq_dec (next bdd) p). subst. unfold upd. unfold next at 2.  
        zify; omega. 
        unfold upd. unfold next at 1. 
        rewrite PMap.gso in H by eauto. 
        apply (wf_lt_next _ _ Hwf) in H; zify; omega. 
      - intros.
        destruct (expr_eq_dec (N (next bdd)) x). 
        + subst; simpl. 
          inversion H. subst. simpl in H1. 
          pose proof Hvl. clear Hvl. 
          pose proof Hvh. clear Hvh. 
          
          rewrite H1.
          rewrite PMap.gss in H1.
          injection H1; intros. destruct H5. destruct H6. destruct H7. simpl. 
          simpl.                  
          destruct (env v). 
          * apply interp_upd. 
            apply Hwf.
            assert (vh = vh0). eapply value_upd_inj; eauto.  subst. eauto. 
          *  apply interp_upd. 
             apply Hwf.
             assert (vl = vl0). eapply value_upd_inj; eauto.  subst. eauto. 
        + apply interp_upd. apply interp_S. apply Hwf.
          apply value_upd_neq; assumption.  
      - intros.
        
        destruct (expr_eq_dec (N (next bdd)) x).
        eapply order_upd_eq in X; eauto. destruct X; subst; eauto.
        eapply order_upd_neq in X; eauto. 
        eapply value_upd_neq in H; eauto. 
        pose proof (wf_value_order _ _ Hwf _ _ H _ X). destruct H0 as [vy Hvy]. exists vy. eauto. 
      - intros. 
        simpl in H. 
        destruct (Pos.eq_dec p (next bdd)); subst. 
        pose proof H.
        rewrite PMap.gss in H. injection H; intros; subst; clear H. 
        exists (if env v then vh else vl). econstructor; eauto. 
        
        rewrite PMap.gso in H by eassumption. apply (wf_find_value env _ Hwf) in H. destruct H.
        eapply value_upd in v0; eauto. 
    Qed. 
    Print Assumptions wf_upd. 
  End wf_upd. 

  Lemma mk_node_correct {env bdd} (Hwf: wf env bdd) {l v h e bdd'}: 
    mk_node bdd l v h = (e,bdd') -> 
    forall vl, value env bdd l vl -> 
    forall vh, value env bdd h vh -> 
          (value env bdd' e (if env v then vh else vl) * incr env bdd bdd')%type.       
  Proof. 
    intros.
    unfold mk_node in H. 
    case_eq (expr_eqb l h). 
    - intros H'; rewrite H' in H. injection H; intros; subst; clear H.
      Lemma expr_eqb_correct e f : expr_eqb e f = true -> e = f.
      Proof.
        destruct e; destruct f; simpl; trivial || (try discriminate).
        intros. f_equal. apply Peqb_true_eq; auto. 
      Qed. 
      apply expr_eqb_correct in H'; subst. 
      assert (vh = vl) by (eapply value_inj; eauto); subst. 
      destruct (env v); split; eauto. 
    - intros H'. rewrite H' in H.
      case_eq (NMap.find (l,v,h) (hmap bdd)); [intros node Hnode | intros Hnode].
      + rewrite Hnode in H.
        injection H; intros; subst; clear H.
        split ; [|auto]. 
        rewrite (wf_bijection _ _ Hwf) in Hnode. econstructor; eauto. 
      + rewrite Hnode in H.
        injection H; intros; subst; clear H.
        refine ((fun H H' => ((H' H), H)) _ _). 
        {                       (* proof of incr *)
          constructor. 
          - apply (order_upd env); auto.  
          - eapply value_upd; eauto. 
          - intros _.
            {
              eapply wf_upd; eauto.  
            }
            
        }
        {
          intros. econstructor; 
                  [
                  | eapply value_upd; eauto
                  | eapply value_upd; eauto
                  ].  
          simpl. apply PMap.gss. 
         }
  Qed.
  Print Assumptions mk_node_correct. 
  Ltac t s ::= 
       repeat 
       ((match goal with 
         | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
         | H : (None = Some _) |- _ => discriminate
         | H : (bind ?F ?G = Some ?X) |- _ => 
           destruct (bind_inversion _ _ F G _ H) as [?x [?I ?I]]; clear H
         | H : (bind2 ?F ?G = Some ?X) |- _ => 
           destruct (bind2_inversion F G _ H) as [?x [?x [?I ?I]]]; clear H
         | |- context [(bind (Some _) ?G)] => simpl
         | H : (bind ?x ?f = None) |- _ => 
           destruct (bind_inversion_None x f H) as [?H | [?x [?I ?I]]]
         | H : ?x = Some ?y |- context [?x] => rewrite H
         | |- (_ * incr ?env ?x ?x)%type => refine ( _ , incr_refl env x )                              
         | H : value ?env ?b T _ |- _ => apply (value_T_inversion env b) in H
         | H : value ?env ?b F _ |- _ => apply (value_F_inversion env b) in H
         | |- value ?env _ T _ => constructor
         | |- value ?env _ F _ => constructor
         | |- _ => subst           
        end) || s); trivial.

  Section cases. 
    Ltac inj :=
      repeat match goal with 
               | H : value ?env ?b ?x ?vx , H' : value ?env ?b ?x ?vy |- _ =>  
                 let H'' := fresh in 
                 assert (H'' := value_inj env b x vx H vy H'); 
                   clear H'; subst
             end. 
    
    Variables
      (env : var -> bool)
      (bdd : BDD)
      (Hwf : wf env bdd)
      (op : bool -> bool -> bool)
      (opb: BDD -> nat -> expr -> expr -> option (expr * BDD))
      (n : nat)
      (IH:  forall bdd : BDD,
              wf env bdd ->
              forall (a b ab : expr) (bdd' : BDD),
                opb bdd n a b = Some (ab, bdd') ->
                forall va : bool,
                  value env bdd a va ->
                  forall vb : bool,
                    value env bdd b vb ->
                    value env bdd' ab (op va vb) * incr env bdd bdd')
      (a b: positive)
      (va vb: bool)
      (Hva : value env bdd (N a) va)
      (Hvb : value env bdd (N b) vb)
      (la : expr) (xa: var) (ha: expr) (Ha : PMap.find a (tmap bdd) = Some (la, xa, ha))
      (lb : expr) (xb: var) (hb: expr) (Hb : PMap.find b (tmap bdd) = Some (lb, xb, hb)).
    
    
    Lemma binop_correct_lt : forall
                               l bdd1 (H1 : opb bdd n la (N b) = Some (l, bdd1))
                               h bdd2 (H2 : opb bdd1 n ha (N b) = Some (h, bdd2))
                               ab bdd3 (H3 : mk_node bdd2 l xa h = (ab, bdd3)),
                               (value env bdd3 ab (op va vb) * incr env bdd bdd3). 
    Proof. 
      intros. 
      destruct (value_N_inversion env bdd a va Hva _ _ _ Ha) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (value_N_inversion env bdd b vb Hvb _ _ _ Hb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hla _ Hwb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf env bdd1) _ _ _ _ H2 
                                       _ (_: value env bdd1 ha vha) 
                                       _ (_: value env bdd1 (N b) _) in _
             ); eauto. 
      inj. 
      refine (let (Hab, Hincr2) := mk_node_correct ( _ : wf env bdd2) H3 _ _ _ _ in _
             ); eauto. 
      destruct (env xa); destruct (env xb); split; eauto. 
    Qed. 
     
    Lemma binop_correct_gt : forall
                               l bdd1 (H1 : opb bdd n (N a) lb  = Some (l, bdd1))
                               h bdd2 (H2 : opb bdd1 n (N a) hb = Some (h, bdd2))
                               ab bdd3 (H3 : mk_node bdd2 l xb h = (ab, bdd3)),
                               (value env bdd3 ab (op va vb) * incr env bdd bdd3). 
    Proof. 
      intros. 
      destruct (value_N_inversion env bdd a va Hva _ _ _ Ha) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (value_N_inversion env bdd b vb Hvb _ _ _ Hb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hwa _ Hlb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf env bdd1) _ _ _ _ H2 
                                       _ (_: value env bdd1 (N a) _) 
                                       _ (_: value env bdd1 hb vhb) in _
             ); eauto. 
      inj. 
      refine (let (Hab, Hincr2) := mk_node_correct _ H3 _ _ _ _ in _
             ); eauto. 
      split. destruct (env xa); destruct (env xb); auto.  
      eauto. 
    Qed.
    
    Lemma binop_correct_eq (Heq: xa = xb) : forall
                               l bdd1 (H1 : opb bdd n la lb  = Some (l, bdd1))
                               h bdd2 (H2 : opb bdd1 n ha hb = Some (h, bdd2))
                               ab bdd3 (H3 : mk_node bdd2 l xa h = (ab, bdd3)),
                               (value env bdd3 ab (op va vb) * incr env bdd bdd3). 
    Proof. 
      intros. subst.  
      destruct (value_N_inversion env bdd a va Hva _ _ _ Ha) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (value_N_inversion env bdd b vb Hvb _ _ _ Hb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hla _ Hlb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf env bdd1) _ _ _ _ H2 
                                       _ (_: value env bdd1 ha vha) 
                                       _ (_: value env bdd1 hb vhb) in _
             ); eauto. 
      inj. 
      refine (let (Hab, Hincr2) := mk_node_correct _ H3 _ _ _ _ in _
             ); eauto. 
      split; destruct (env xb); eauto.  
    Qed. 
  End cases. 

  Lemma andb_correct env bdd (Hwf: wf env bdd) n a b ab bdd' :
    andb bdd n a b = Some (ab, bdd') ->
    forall va, value env bdd a va -> 
          forall vb, value env bdd b vb -> 
                (value env bdd' ab (va && vb)%bool * incr env bdd bdd').
  Proof.
    revert bdd Hwf a b ab bdd'. 
    induction n; intros bdd Hwf a b ab bdd' Hand va Hva vb Hvb. 
    - discriminate. 
    - simpl in Hand. 
      Ltac s := 
        try match goal with 
          | |- context [(_ && false)%bool]  => rewrite Bool.andb_comm; simpl Datatypes.andb
          | |- context [(_ && true)%bool]  => rewrite Bool.andb_comm; simpl  Datatypes.andb
          | |- context [(false && _ )%bool]  => simpl  Datatypes.andb
          | |- context [(true  && _ )%bool]  => simpl  Datatypes.andb
        end.  
      destruct a as [ | | a]; destruct b as [ | | b]; simpl in *; t s.  
      destruct x as [[la xa] ha]. destruct x0 as [[lb xb] hb]. 
      destruct (NPeano.Nat.compare xa xb) eqn: Heq.
      + apply nat_compare_eq in Heq; subst; t s. 
        eauto using binop_correct_eq. 
      + t s; eauto using binop_correct_lt.
        
      + t s; eauto using binop_correct_gt. 
  Qed.

  Print Assumptions andb_correct. 

  Lemma orb_correct env bdd (Hwf: wf env bdd) n a b ab bdd' :
    orb bdd n a b = Some (ab, bdd') ->
    forall va, value env bdd a va -> 
    forall vb, value env bdd b vb -> 
    (value env bdd' ab (va || vb)%bool * incr env bdd bdd').
  Proof.
    revert bdd Hwf a b ab bdd'. 
    induction n; intros bdd Hwf a b ab bdd' Hand va Hva vb Hvb. 
    - discriminate. 
    - simpl in Hand. 
    Ltac s ::= 
         try 
         match goal with 
          | |- context [(_ || false)%bool]  => rewrite Bool.orb_comm; simpl Datatypes.orb
          | |- context [(_ || true)%bool]  => rewrite Bool.orb_comm; simpl  Datatypes.orb
          | |- context [(false || _ )%bool]  => simpl  Datatypes.orb
          | |- context [(true  || _ )%bool]  => simpl  Datatypes.orb
         end.
    destruct a as [ | | a]; destruct b as [ | | b]; simpl in *; t s.
    destruct x as [[la xa] ha]. destruct x0 as [[lb xb] hb]. 
    destruct (NPeano.Nat.compare xa xb) eqn: Heq.
      + apply nat_compare_eq in Heq; subst; t s. 
        eauto using binop_correct_eq. 
      + t s; eauto using binop_correct_lt.        
      + t s; eauto using binop_correct_gt.
  Qed.  

  Lemma negb_correct env bdd (Hwf: wf env bdd) n a a' bdd' :
    negb bdd n a = Some (a', bdd') ->
    forall va, value env bdd a va -> 
    (value env bdd' a' (Datatypes.negb va)%bool * incr env bdd bdd').
  Proof.
    revert bdd Hwf a a' bdd'. 
    induction n; intros bdd Hwf a a' bdd' Hnegb va Hva. 
    - discriminate. 
    - simpl in Hnegb. 
    Ltac s ::= 
         try
         match goal with 
          | |- context [(Datatypes.negb false)%bool] =>  simpl Datatypes.negb 
          | |- context [(Datatypes.negb true)%bool]  =>  simpl Datatypes.negb
         end. 
    destruct a as [ | | a]; simpl in *; t s.
    destruct x as [[la xa] ha]; t s.
    destruct (value_N_inversion env bdd a va Hva _ _ _ I) as [vla [vha [[Hla Hha] Hwa]]].
    destruct (IHn _ Hwf _ _ _ I1 _ Hla) as [Hvx Hincr]; clear I1. 
    refine (let (Hvx1,Hincr2) := IHn x0 (_ : wf env x0) _ _ _ I0 
                             _ (_: value env _ ha vha) 
                             in _
               ); eauto.
    pose proof (value_inj _ _ _ _ Hva _ Hwa); subst. 
    refine (let (Hab, Hincr2) := mk_node_correct (_ : wf env x2) H _ _ _ _ in _
           ); eauto. 
    split; destruct (env xa); eauto. 
  Qed.

  Lemma xorb_correct env bdd (Hwf: wf env bdd) n a b ab bdd' :
    xorb bdd n a b = Some (ab, bdd') ->
    forall va, value env bdd a va -> 
    forall vb, value env bdd b vb -> 
    (value env bdd' ab (Datatypes.xorb va vb)%bool * incr env bdd bdd').
  Proof.
    revert bdd Hwf a b ab bdd'. 
    induction n; intros bdd Hwf a b ab bdd' Hand va Hva vb Hvb. 
    - discriminate. 
    - simpl in Hand. 
      Ltac s ::= 
      repeat 
        match goal with 
          | |- context [(Datatypes.xorb _ false)%bool]  => rewrite Bool.xorb_false_r
          | |- context [(Datatypes.xorb _ true)%bool]  => rewrite Bool.xorb_true_r
          | |- context [(Datatypes.xorb false  _ )%bool]  => rewrite Bool.xorb_false_l
          | |- context [(Datatypes.xorb true _ )%bool]  => rewrite Bool.xorb_true_l                   
        end.
    destruct a as [ | | a]; destruct b as [ | | b]; simpl in *; t s; eauto using negb_correct. 
    
    destruct x as [[la xa] ha]. destruct x0 as [[lb xb] hb]. 
    destruct (NPeano.Nat.compare xa xb) eqn: Heq.
      + apply nat_compare_eq in Heq; subst; t s. 
        eauto using binop_correct_eq. 
      + t s; eauto using binop_correct_lt. 
      + t s; eauto using binop_correct_gt. 
  Qed.
End Inner.

Record BDD := 
  mk
    {
      content:> Inner.BDD;
      wf : forall env,  Inner.wf env content
    }.

Section t.   
  Variable env : nat -> bool. 
  Let depth (bdd: BDD) := (Inner.wf_depth env bdd (wf bdd env)). 

  Definition interp bdd  (a: expr) : option bool :=
    Inner.interp env (content bdd) (depth bdd) a. 
  
  Definition andb bdd a b : option (expr * BDD):=
    do e, r <- Inner.andb (content bdd) (depth bdd) a b;
    Some (e, mk _ _).
  Next Obligation. 
    unfold andb_obligation_1. 
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
    let (e, r) := Inner.mk_var (content bdd) x in 
    (e, mk r (S (max x (depth bdd)))). 
  
  Section props. 
    Variable env : var -> bool. 
    Lemma andb_correct bdd a b : 
      forall va, interp bdd a = Some va -> 
      forall vb, interp bdd b = Some vb -> 
      forall ab bdd', andb bdd a b = Some (ab, bdd') -> 
                 interp bdd' ab = 
      
      
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