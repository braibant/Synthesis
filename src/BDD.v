Require Import Common ZArith. 

(** This file defines a library of BDDs implemented in Coq. This
implementation is proved correct, but not complete: that is, we do not
prove that two expressions that are equal are injected to the same
node in the BDD. *)

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

(** We are now ready to start speaking about BDDs. 
    [tmap] is a map from indexes to nodes;
    [hmap] is used to hash-cons nodes;
    [next] is the index of the next usable node.  

    All the nodes below than [next] have a value: this means that
    the graph underlying [hmap] is acyclic, yet we do not express
    that fact (this maybe a good idea to express that fact in the
    invariant.)  *)

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

(** [mk_node bdd l v h] creates a node corresponding to the triple [l,v,h] if needed. *)

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

    (** All the binary operations on the bdd follow the same
    structure. We define partial operations that use an explicit
    bound on the number of recursive calls, and fail if that number
    is not sufficent. We cannot easily use open-recursion and a
    common skeleton for these operations, as we would in OCaml
    (problem of termination), and this is the reason why the code is
    verbose.

    Note that we cannot esasily use Program or Function, because we use
    nested calls to the function we define (that is, the
    well-founded relation that terminates shall mention the fact
    that our bdds are well-formed, and refinements of each other)*)

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
    
    Definition ite bdd n c l r:=
      do cl, bdd  <- andb bdd n c l;
      do nc, bdd  <- negb bdd n c;
      do ncr, bdd <- andb bdd n nc r;
      orb bdd n cl ncr.
    
  End operations.
  
  
  (** This is the base inductive that defines the value that is
  associated to any expression within the [bdd]. *)

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


Inductive path bdd : expr -> Type :=
| path_F : path bdd F
| path_T : path bdd T
| path_N : forall p l v h, 
             PMap.find p (tmap bdd) = Some (l,v,h) -> 
             path bdd l -> 
             path bdd h -> 
             path bdd (N p). 

Inductive depth bdd : expr -> nat -> Type  :=
| depth_F : forall n, depth bdd F n
| depth_T : forall n, depth bdd T n
| depth_N : forall n p l v h, 
              PMap.find p (tmap bdd) = Some (l,v,h) -> 
              depth bdd l n -> 
              depth bdd h n -> 
              depth bdd (N p) (S n).  

(** Our bdds are well-formed, according to the following
definition. As was hinted at before, we could have used another
invariant here (making the acyclicity/well-foundedness more
explicit). *)

Class wf (b: BDD) : Type :=
  {
    wf_bijection : forall p n, NMap.find n (hmap b) = Some p 
                          <-> PMap.find p (tmap b) = Some n;
    wf_lt_next : forall p x, PMap.find p (tmap b) = Some x -> 
                        (p < next b)%positive;
    wf_lt_next_find : forall p, (p < next b)%positive ->
                        {x : node | PMap.find p (tmap b) = Some x};                         
    (* wf_depth : nat; *)

    (* path is a correct and complete caracterisation of the elements that are in the BDD *)
    
    wf_lt_path: forall p, (p < next b)%positive ->  path b (N p); 
    wf_path_lt: forall p, path b (N p) -> (p < next b)%positive
    (* wf_path_depth : forall p (path_p: path b p), depth b p wf_depth *)
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

Class incr (b1 b2 : BDD) :=
  {
    incr_map: forall p x, PMap.find p (tmap b1) = Some x -> PMap.find p (tmap b2) = Some x;
    incr_order : forall x y, order b1 x y -> order b2 x y;
    incr_path : forall x, path b1 x -> path b2 x;
    incr_wf : wf b1 -> wf b2 
  }.

Hint Resolve incr_path incr_order incr_wf. 
  
Lemma incr_refl bdd : incr bdd bdd. 
Proof. 
  constructor; tauto. 
Qed. 

Lemma incr_trans  a b c : incr a b -> incr b c -> incr a c. 
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

Lemma value_upd  env bdd (Hwf: wf bdd) l v h:
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

Lemma path_upd  bdd (Hwf: wf bdd) l v h:
  NMap.find (l,v,h) (hmap bdd) = None ->
  path bdd l -> 
  path bdd h -> 
  forall x, path bdd x  -> 
  path (upd bdd (l,v,h)) x. 
Proof.              
  intros Hbdd Hvl Hvh x H.
  induction H. 
  constructor. 
  constructor. 
  apply (path_N _ _ l0 v0 h0); auto. 
  simpl. rewrite PMap.gso. apply e.
  destruct Hwf as [ _ Hwf]. apply Hwf in e. clear - e. zify; omega. 
Qed. 
Hint Resolve path_upd.   

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

Remark wf_neq bdd (Hwf : wf bdd) p x : PMap.find p (tmap bdd) = Some x -> p <> next bdd. 
Proof. 
  intros H. apply (wf_lt_next)  in H; auto.  zify; omega. 
Qed. 
Hint Resolve wf_neq. 


(* Lemma value_upd_inj x vx vy : value env bdd x vx ->  *)
(*                               value env (upd bdd (l,v,h)) x vy ->  *)
(*                               vx = vy.  *)
(* Proof. *)
(*   intros.  *)
(*   eapply value_upd in H; eauto.  *)
(* Qed.  *)
      
Lemma order_path bdd x y : path bdd x -> order bdd x y -> path bdd y. 
Proof. 
  intros. 
  inversion H; subst. 
  compute in X; intuition; discriminate. 
  compute in X; intuition; discriminate.
  unfold order in X. destruct X. simpl in e. rewrite H0 in e. injection e; intros; subst. auto. 
  simpl in e. rewrite H0 in e. injection e; intros; subst. auto. 
Qed. 
  
Section wf_upd.  
  Variable bdd : BDD. 
  Hypothesis Hwf : wf bdd.
  Variable (l:expr) (v:nat) (h:expr). 
  Hypothesis Hvl : path bdd l. 
  Hypothesis Hvh : path bdd h. 
  Hypothesis Hnode : NMap.find (elt:=positive) (l, v, h) (hmap bdd) = None.

  (* Remark value_upd_left : value env (upd bdd (l,v,h)) l vl.  *)
  (* Proof.  *)
  (*   eapply value_upd; eauto.  *)
  (* Qed.  *)
  (* Remark value_upd_right : value env (upd bdd (l,v,h)) h vh.  *)
  (* Proof.  *)
  (*   eapply value_upd; eauto.  *)
  (* Qed.  *)
  Remark path_upd_left :  path  (upd bdd (l,v,h)) l.
  Proof.
    eapply path_upd; eauto.
  Qed.
  Remark path_upd_right : path (upd bdd (l,v,h)) h.
  Proof.
    eapply path_upd; eauto.
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
         
  Lemma interp_upd env : forall (n : var) (x : expr) (y : bool),
                       interp env bdd n x = Some y -> interp env (upd bdd (l, v, h)) n x = Some y.
  Proof.
    induction n; intros. discriminate.
    simpl in *.
    destruct x; intuition.
    t; destruct x as [[l2 v2] h2]; t.
    
    rewrite PMap.gso by eauto. setoid_rewrite h0; simpl.
    destruct (env v2) eqn: Heq;t; intuition.
  Qed.
    
  Lemma wf_value_lt env x vx : value env bdd (N x) vx -> 
                           (x < next bdd)%positive. 
  Proof.
    clear - Hwf. 
    intros H. inversion H.  subst.
    apply (wf_lt_next) in H1. auto. 
  Qed. 
  
  Hint Resolve wf_value_lt.
  Hint Resolve wf_path_lt.
  (* Lemma value_upd_neq x vx :  value env (upd bdd (l, v, h)) x vx -> *)
  (*                             N (next bdd) <> x -> *)
  (*                             value env bdd x vx. *)
  (* Proof. *)
  (*   intros.  *)
  (*   induction H;  auto.  *)
  (*   simpl in e. rewrite PMap.gso in e by congruence.  *)
  (*   destruct (wf_find_value _ _ Hwf  _ _ e) as [vp Hvp].  *)

  (*   refine (let IH1 := IHvalue1 _ in  *)
  (*           let IH2 := IHvalue2 _ in _).  *)
  (*   destruct l0 as [ | | X ]; try discriminate;   *)
  (*   assert (HX : (X < next bdd)%positive) by *)
  (*       (refine (let H := wf_value_order _ _ Hwf _ _ Hvp  (N X) _ in  *)
  (*                let (x, Hx) := H in wf_value_lt _ _ Hx  *)
  (*              ); [eauto ]).  *)
  (*   clear - HX. intros H; injection H; clear H. zify; omega.  *)
  (*   destruct h0 as [ | | X ]; try discriminate;   *)
  (*   assert (HX : (X < next bdd)%positive) by *)
  (*       (refine (let H := wf_value_order _ _ Hwf _ _ Hvp  (N X) _ in  *)
  (*                let (x, Hx) := H in wf_value_lt _ _ Hx  *)
  (*              ); [eauto ]).  *)
  (*   clear - HX. intros H; injection H; clear H; intros. zify; omega.  *)
  (*   econstructor; eauto.  *)
  (* Qed. *)
  
  Hint Constructors path. 

  Lemma path_upd_neq x :  path (upd bdd (l, v, h)) x  ->
                              N (next bdd) <> x ->
                              path bdd x.
  Proof. 
    intros. induction H; auto. 
    simpl in e. rewrite PMap.gso in e by congruence.
    
    refine (let IH1 := IHpath1 _ in
            let IH2 := IHpath2 _ in _); clear IHpath1 IHpath2. 
    
    destruct l0 as [ | | X ]; try discriminate. 
    assert (HX : (X < next bdd)%positive). 
    eauto 6 using wf_path_lt, wf_lt_path, wf_lt_next, order_path. 
    intros H'.  injection H'. subst.   zify. omega. 

    destruct h0 as [ | | X ]; try discriminate. 
    assert (HX : (X < next bdd)%positive). 
    eauto 6 using wf_path_lt, wf_lt_path, wf_lt_next, order_path. 
    intros H'.  injection H'. subst.   zify. omega. 

    econstructor; eauto. 
  Qed.
  
  (* Lemma value_upd_eq x vx : value env (upd bdd (l,v,h)) x vx -> *)
  (*                           x = N (next bdd) ->  *)
  (*                           value env (upd bdd (l,v,h)) x (if env v then vh else vl).  *)
  
  Lemma order_upd_eq env x y : order (upd bdd (l,v,h)) x y -> 
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
  
  Lemma order_upd_neq env x y : order (upd bdd (l,v,h)) x y -> 
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
  
  Lemma wf_upd : wf (upd bdd (l, v, h)).
  Proof. 
    apply Build_wf. 
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
          rewrite <- (wf_bijection) in H; congruence. 
        * apply node_compare_refl. 
      + rewrite NMapFacts.add_neq_o by (rewrite node_compare_eq_iff; tauto).
        split; intros. 
        rewrite (wf_bijection) in H. 
        rewrite PMap.gso; eauto. 
        rewrite PMap.gso in H. 
        rewrite (wf_bijection); auto. 

        intros Hp. subst. 
        rewrite PMap.gss in H. congruence. 

    - intros. 
      simpl in H. 
      destruct (Pos.eq_dec (next bdd) p). subst. unfold upd. unfold next at 2.  
      zify; omega. 
      unfold upd. unfold next at 1. 
      rewrite PMap.gso in H by eauto. 
      apply (wf_lt_next) in H; zify; omega. 
    - intros. 
      {
        unfold upd in H. unfold next at 1 in H. 
        destruct (Pos.eq_dec p (next bdd)). subst. simpl. 
        exists (l,v,h). rewrite PMap.gss. reflexivity. 
        assert ((p < next bdd)%positive). 
        zify;omega. 
        destruct (wf_lt_next_find _ H0) as [x Hx]. 
        exists x. simpl. rewrite PMap.gso by eauto. auto. 
      }
    - intros. 
      destruct (Pos.eq_dec (next bdd) (p)). 
      + subst.
        apply (path_N _ (next bdd) l v h); auto.  simpl. rewrite PMap.gss; reflexivity.
      + apply path_upd; auto. apply wf_lt_path. unfold upd in H. unfold next at 1 in H.  zify. omega. 
    - intros. 
      destruct (Pos.eq_dec (next bdd) (p)). 
      + subst. unfold upd.  unfold next at 2. zify; omega. 
      + subst. unfold upd.  unfold next at 1. 
        apply path_upd_neq in H.  2: congruence.  
        apply wf_path_lt in H. zify;omega. 
  Qed. 
End wf_upd. 

Lemma mk_node_correct {env bdd} (Hwf: wf  bdd) {l v h e bdd'}: 
  mk_node bdd l v h = (e,bdd') -> 
  forall vl, value env bdd l vl -> 
  forall vh, value env bdd h vh -> 
        (value env bdd' e (if env v then vh else vl) * incr  bdd bdd')%type.       
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
      rewrite (wf_bijection ) in Hnode. econstructor; eauto. 
    + rewrite Hnode in H.
      injection H; intros; subst; clear H.
      assert (incr bdd (upd bdd (l,v,h))). 
      {constructor.
       * intros. 
         simpl. rewrite PMap.gso; auto.  
         apply wf_lt_next in H. zify;omega.         
       * apply (order_upd); auto.  
       * eapply path_upd; eauto. 
         Lemma path_of_value env bdd x vx : 
           value env bdd x vx -> 
           path bdd x. 
         Proof. 
           induction 1; try constructor. 
           econstructor. apply e. auto.  auto. 
         Qed. 
         Hint Resolve path_of_value. 
         eauto. 
         eauto. 
       * intros. eapply wf_upd; eauto.  
      }      
      
      { split; auto. 
        intros. econstructor; 
                [
                | eapply value_upd; eauto
                | eapply value_upd; eauto
                ].  
        simpl. apply PMap.gss. 
       }
Qed.
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
       | |- (_ * incr ?x ?x)%type => refine ( _ , incr_refl x )                              
       | H : value ?env ?b T _ |- _ => apply (value_T_inversion env b) in H
       | H : value ?env ?b F _ |- _ => apply (value_F_inversion env b) in H
       | |- value ?env _ T _ => constructor
       | |- value ?env _ F _ => constructor
       | |- _ => subst           
      end) || s); trivial.
Lemma incr_value env bdd1 bdd2 x vx (Hincr:incr bdd1 bdd2) :
  value env bdd1 x vx -> 
  value env bdd2 x vx. 
Proof.   
  induction 1; try constructor. 
  econstructor; eauto using incr_map.  
Qed. 

Hint Resolve incr_value.   
Section value. 
  Section binop. 
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
      (Hwf : wf bdd)
      (op : bool -> bool -> bool)
      (opb: BDD -> nat -> expr -> expr -> option (expr * BDD))
      (n : nat)
      (IH:  forall bdd : BDD,
              wf  bdd ->
              forall (a b ab : expr) (bdd' : BDD),
                opb bdd n a b = Some (ab, bdd') ->
              forall va : bool,
                value env bdd a va ->
                forall vb : bool,
                  value env bdd b vb ->
                  value env bdd' ab (op va vb) * incr  bdd bdd')
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
                               (value env bdd3 ab (op va vb) * incr  bdd bdd3). 
    Proof. 
      intros. 
      destruct (value_N_inversion env bdd a va Hva _ _ _ Ha) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (value_N_inversion env bdd b vb Hvb _ _ _ Hb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hla _ Hwb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf  bdd1) _ _ _ _ H2 
                                      _ (_: value env bdd1 ha vha) 
                                      _ (_: value env bdd1 (N b) _) in _
             ); eauto. 
      
      inj. 
      refine (let (Hab, Hincr2) := mk_node_correct ( _ : wf bdd2) H3 _ _ _ _ in _
             ); eauto. 
      destruct (env xa); destruct (env xb); split; eauto. 
    Qed. 
    
    Lemma binop_correct_gt : forall
                               l bdd1 (H1 : opb bdd n (N a) lb  = Some (l, bdd1))
                               h bdd2 (H2 : opb bdd1 n (N a) hb = Some (h, bdd2))
                               ab bdd3 (H3 : mk_node bdd2 l xb h = (ab, bdd3)),
                               (value env bdd3 ab (op va vb) * incr bdd bdd3). 
    Proof. 
      intros. 
      destruct (value_N_inversion env bdd a va Hva _ _ _ Ha) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (value_N_inversion env bdd b vb Hvb _ _ _ Hb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hwa _ Hlb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf  bdd1) _ _ _ _ H2 
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
                                              (value env bdd3 ab (op va vb) * incr bdd bdd3). 
    Proof. 
      intros. subst.  
      destruct (value_N_inversion env bdd a va Hva _ _ _ Ha) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (value_N_inversion env bdd b vb Hvb _ _ _ Hb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hla _ Hlb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf bdd1) _ _ _ _ H2 
                                      _ (_: value env bdd1 ha vha) 
                                      _ (_: value env bdd1 hb vhb) in _
             ); eauto. 
      inj. 
      refine (let (Hab, Hincr2) := mk_node_correct _ H3 _ _ _ _ in _
             ); eauto. 
      split; destruct (env xb); eauto.  
    Qed. 
  End binop.  

  Lemma andb_correct env bdd (Hwf: wf bdd) n a b ab bdd' :
    andb bdd n a b = Some (ab, bdd') ->
    forall va, value env bdd a va -> 
          forall vb, value env bdd b vb -> 
                (value env bdd' ab (va && vb)%bool * incr bdd bdd').
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
  
  
  Lemma orb_correct env bdd (Hwf: wf bdd) n a b ab bdd' :
    orb bdd n a b = Some (ab, bdd') ->
    forall va, value env bdd a va -> 
          forall vb, value env bdd b vb -> 
                (value env bdd' ab (va || vb)%bool * incr bdd bdd').
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
  
  Lemma negb_correct env bdd (Hwf: wf bdd) n a a' bdd' :
    negb bdd n a = Some (a', bdd') ->
    forall va, value env bdd a va -> 
          (value env bdd' a' (Datatypes.negb va)%bool * incr bdd bdd').
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
      refine (let (Hvx1,Hincr2) := IHn x0 (_ : wf x0) _ _ _ I0 
                                       _ (_: value env _ ha vha) 
              in _
             ); eauto.
      pose proof (value_inj _ _ _ _ Hva _ Hwa); subst. 
      refine (let (Hab, Hincr2) := mk_node_correct (_ : wf x2) H _ _ _ _ in _
             ); eauto. 
      split; destruct (env xa); eauto. 
  Qed.
  
  Lemma xorb_correct env bdd (Hwf: wf bdd) n a b ab bdd' :
    xorb bdd n a b = Some (ab, bdd') ->
    forall va, value env bdd a va -> 
          forall vb, value env bdd b vb -> 
                (value env bdd' ab (Datatypes.xorb va vb)%bool * incr bdd bdd').
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
  
 
  Lemma mk_var_correct env bdd (Hwf: wf bdd) v ptr bdd' :
    mk_var bdd v = (ptr, bdd') -> 
    value env bdd' ptr (env v) * incr bdd bdd'. 
  Proof. 
    unfold mk_var. intros. 
    eapply (@mk_node_correct env) in H; eauto.  
    destruct (env v); apply H. 
  Qed. 
  

End value. 

Inductive pvalue env bdd : expr -> bool -> Type :=
| pvalue_T : pvalue env bdd T true
| pvalue_F : pvalue env bdd F false
| pvalue_N : forall (p : positive) (l : expr) (v : var) (h : expr),
               PMap.find p (tmap bdd) = Some (l, v, h) ->
               forall vl : bool,
                 pvalue env bdd l vl ->
                 forall vh : bool,
                   pvalue env bdd h vh ->
                   forall (r: bool), List.nth_error env v = Some r ->  
                                pvalue env bdd (N p) (if r then vh else vl). 

Hint Constructors pvalue. 

Lemma list_nth_error_length {A} l (x: A):             
       List.nth_error (l ++ [x]) (List.length l) = Some x. 
Proof. 
  induction l. reflexivity. 
  tauto. 
Qed. 

Lemma pvalue_env_snoc bdd env x vx e : 
  pvalue env bdd x vx -> 
  pvalue (env ++ [e]) bdd x vx. 
Proof. 
  induction 1; auto. 
  econstructor; eauto.  
  Lemma list_nth_error_length_2 {A} l (x:A): 
    forall v r, List.nth_error l v = Some r -> 
         List.nth_error (l ++ [x]) v = Some r.  
  Proof. 
    induction l. 
    destruct v; try discriminate.  
    destruct v. simpl. tauto. 
    intros. simpl. simpl in H. intuition. 
  Qed. 
  apply list_nth_error_length_2; auto. 
Qed. 

Lemma pvalue_incr bdd bdd' (Hincr: incr bdd bdd') env : 
  forall x vx, 
  pvalue env bdd x vx -> 
  pvalue env bdd' x vx. 
Proof. 
  induction 1; auto. 
  econstructor; eauto.  
  apply Hincr. auto. 
Qed. 

Hint Resolve pvalue_incr. 
Lemma pvalue_inj bdd env x vx:  
  pvalue env bdd x vx -> 
  forall vx' , pvalue env bdd x vx' -> 
  vx = vx'. 
Proof. 
  induction 1. 
  inversion 1. reflexivity. 
  inversion 1; reflexivity. 
  intros v2 Hv2. 
  inversion Hv2. 
  simpl in *. 
  rewrite e in H2. inject H2. 
  rewrite H5 in e0. inject e0. 
  specialize (IHpvalue1 _ H3); clear H0 H3. 
  specialize (IHpvalue2 _ H4); clear H H4. 
  subst. reflexivity. 
Qed. 

Lemma pvalue_N_inversion :
  forall env (bdd : BDD) (a : positive) (va : bool),
    pvalue env bdd (N a) va ->
    forall (l : expr) (x : var) (h : expr),
      PMap.find a (tmap bdd) = Some (l, x, h) ->
      forall vx, List.nth_error env x = Some vx -> 
            {vl : bool &
                       {vh : bool &
                                  (pvalue env bdd l vl * pvalue env bdd h vh *
                                   pvalue env bdd (N a) (if vx then vh else vl))%type}}. 
Proof.   
  intros. 
  inversion H; subst. 
  rewrite H0 in H3; inject H3. 
  rewrite H1 in H6; inject H6. 
  repeat eexists; eauto. 
Qed. 

Section pvalue. 
  Lemma pvalue_upd  env bdd (Hwf: wf bdd) l v h:
    NMap.find (l,v,h) (hmap bdd) = None ->
    forall vl, pvalue env bdd l vl -> 
          forall vh, pvalue env bdd h vh -> 
                forall x vx, pvalue env bdd x vx -> 
                        pvalue env (upd bdd (l,v,h)) x vx. 
  Proof.              
    intros Hbdd vl Hvl vh Hvh x vx H.
    induction H. 
    constructor. 
    constructor. 
    econstructor; eauto. 
    simpl. rewrite PMap.gso. auto. 
    destruct Hwf as [ _ Hwf]. apply Hwf in e. clear - e. zify; omega. 
  Qed. 
  Hint Resolve pvalue_upd.   

  Lemma mk_node_pcorrect {env bdd} (Hwf: wf  bdd) {l v h e bdd'}: 
    mk_node bdd l v h = (e,bdd') -> 
    forall r, List.nth_error env v = Some r -> 
    forall vl, pvalue env bdd l vl -> 
          forall vh, pvalue env bdd h vh -> 
                (pvalue env bdd' e (if r then vh else vl) * incr  bdd bdd')%type.       
  Proof. 
    intros.
    unfold mk_node in H. 
    case_eq (expr_eqb l h). 
    - intros H'; rewrite H' in H. inject H.  
      apply expr_eqb_correct in H'; subst. 
      assert (vh = vl) by (eapply pvalue_inj; eauto); subst. 
      destruct r;  split; eauto. 
    - intros H'. rewrite H' in H.
      case_eq (NMap.find (l,v,h) (hmap bdd)); [intros node Hnode | intros Hnode].
    + rewrite Hnode in H.
      injection H; intros; subst; clear H.
      split ; [|auto]. 
      rewrite (wf_bijection ) in Hnode. econstructor; eauto. 
    + rewrite Hnode in H.
      injection H; intros; subst; clear H.
      assert (incr bdd (upd bdd (l,v,h))). 
      {constructor.
       * intros. 
         simpl. rewrite PMap.gso; auto.  
         apply wf_lt_next in H. zify;omega.         
       * apply (order_upd); auto.  
       * eapply path_upd; eauto.
         Lemma path_of_pvalue env bdd x vx : 
           pvalue env bdd x vx -> 
           path bdd x. 
         Proof. 
           induction 1; try constructor. 
           econstructor. apply e. auto.  auto. 
         Qed. 
         Hint Resolve path_of_pvalue. 
 
         eauto. 
         eauto. 
       * intros. eapply wf_upd; eauto.  
      }      
      
      { split; auto. 
        intros.
        econstructor;
                [
                | eapply pvalue_upd; eauto
                | eapply pvalue_upd; eauto
                | eauto].  
        simpl. apply PMap.gss. 
       }
Qed.
  Lemma pvalue_inv_env bdd env a va l x h :
    PMap.find a (tmap bdd) = Some (l,x,h) -> 
    pvalue env bdd (N a) va -> 
    { vx |  List.nth_error env x = Some vx}. 
  Proof. 
    intros. 
    inversion H0; subst. 
    rewrite H in H2; inject H2. 
    subst. eexists. apply H5.   
  Qed. 
  Hint Resolve pvalue_inv_env.
  Section binop. 
    Ltac inj :=
      repeat match goal with 
               | H : pvalue ?env ?b ?x ?vx , H' : pvalue ?env ?b  ?x ?vy |- _ =>  
                 let H'' := fresh in 
                 assert (H'' := pvalue_inj b env x vx H vy H'); 
                   clear H'; subst
             end. 
    
    Variables
      (env : list bool)
      (bdd : BDD)
      (Hwf : wf bdd)
      (op : bool -> bool -> bool)
      (opb: BDD -> nat -> expr -> expr -> option (expr * BDD))
      (n : nat)
      (IH:  forall bdd : BDD,
              wf  bdd ->
              forall (a b ab : expr) (bdd' : BDD),
                opb bdd n a b = Some (ab, bdd') ->
              forall va : bool,
                pvalue env bdd a va ->
                forall vb : bool,
                  pvalue env bdd b vb ->
                  pvalue env bdd' ab (op va vb) * incr  bdd bdd')
      (a b: positive)
      (va vb: bool)
      (Hva : pvalue env bdd (N a) va)
      (Hvb : pvalue env bdd (N b) vb)
      (la : expr) (xa: var) (ha: expr) (Ha : PMap.find a (tmap bdd) = Some (la, xa, ha)) 
      (lb : expr) (xb: var) (hb: expr) (Hb : PMap.find b (tmap bdd) = Some (lb, xb, hb)).   
  
    Lemma binop_pcorrect_lt : forall
                               l bdd1 (H1 : opb bdd n la (N b) = Some (l, bdd1))
                               h bdd2 (H2 : opb bdd1 n ha (N b) = Some (h, bdd2))
                               ab bdd3 (H3 : mk_node bdd2 l xa h = (ab, bdd3)),
                               (pvalue env bdd3 ab (op va vb) * incr  bdd bdd3). 
    Proof. 
      intros. 
      destruct (pvalue_inv_env _ _ _ _ _ _ _ Ha Hva) as [vxa Hxa]. 
      destruct (pvalue_inv_env _ _ _ _ _ _ _ Hb Hvb) as [vxb Hxb]. 
      destruct (pvalue_N_inversion env bdd a va Hva _ _ _ Ha _ Hxa) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (pvalue_N_inversion env bdd b vb Hvb _ _ _ Hb _ Hxb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hla _ Hwb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf  bdd1) _ _ _ _ H2 
                                      _ (_: pvalue env bdd1 ha vha) 
                                      _ (_: pvalue env bdd1 (N b) _) in _
             ); eauto. 
      inj. 
      refine (let (Hab, Hincr2) := mk_node_pcorrect ( _ : wf bdd2) H3 _ _ _ _ _ _ in _
             ); eauto. 
      destruct (vxa); destruct (vxb); split; eauto.   
    Qed. 
    
    Lemma binop_pcorrect_gt : forall
                               l bdd1 (H1 : opb bdd n (N a) lb  = Some (l, bdd1))
                               h bdd2 (H2 : opb bdd1 n (N a) hb = Some (h, bdd2))
                               ab bdd3 (H3 : mk_node bdd2 l xb h = (ab, bdd3)),
                               (pvalue env bdd3 ab (op va vb) * incr bdd bdd3). 
    Proof. 
      intros.  
      destruct (pvalue_inv_env _ _ _ _ _ _ _ Ha Hva) as [vxa Hxa]. 
      destruct (pvalue_inv_env _ _ _ _ _ _ _ Hb Hvb) as [vxb Hxb]. 
      destruct (pvalue_N_inversion env bdd a va Hva _ _ _ Ha _ Hxa) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (pvalue_N_inversion env bdd b vb Hvb _ _ _ Hb _ Hxb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hwa _ Hlb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf  bdd1) _ _ _ _ H2 
                                      _ (_: pvalue env bdd1 (N a) _) 
                                      _ (_: pvalue env bdd1 hb vhb) in _
             ); eauto. 
      inj. 
      refine (let (Hab, Hincr2) := mk_node_pcorrect ( _ : wf bdd2) H3 _ _ _ _ _ _ in _
             ); eauto. 
      destruct (vxa); destruct (vxb); split; eauto.  
    Qed.
  
    Lemma binop_pcorrect_eq (Heq: xa = xb) : forall
                                              l bdd1 (H1 : opb bdd n la lb  = Some (l, bdd1))
                                              h bdd2 (H2 : opb bdd1 n ha hb = Some (h, bdd2))
                                              ab bdd3 (H3 : mk_node bdd2 l xa h = (ab, bdd3)),
                                              (pvalue env bdd3 ab (op va vb) * incr bdd bdd3). 
    Proof. 
      intros. 
      destruct (pvalue_inv_env _ _ _ _ _ _ _ Ha Hva) as [vxa Hxa]. 
      destruct (pvalue_inv_env _ _ _ _ _ _ _ Hb Hvb) as [vxb Hxb]. 
      subst.  rewrite Hxb in Hxa; inject Hxa. 
      destruct (pvalue_N_inversion env bdd a va Hva _ _ _ Ha _ Hxb) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (pvalue_N_inversion env bdd b vb Hvb _ _ _ Hb _ Hxb) as [vlb [vhb [[Hlb Hhb] Hwb]]].
      destruct (IH _ Hwf _ _ _ _ H1 _ Hla _ Hlb) as [Hvx Hincr]. 
      refine (let (Hvx1,Hincr2) := IH bdd1 (_ : wf bdd1) _ _ _ _ H2 
                                      _ (_: pvalue env bdd1 ha vha) 
                                      _ (_: pvalue env bdd1 hb vhb) in _
             ); eauto. 
      inj. 
      refine (let (Hab, Hincr2) := mk_node_pcorrect _ H3 _ _ _ _ _ _  in _
             ); eauto.
      split; destruct (vxa); eauto.  
    Qed. 
  End binop.  

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
       | |- (_ * incr ?x ?x)%type => refine ( _ , incr_refl x )                              
       | H : pvalue ?env ?b T _ |- _ => inversion_clear H
       | H : pvalue ?env ?b F _ |- _ => inversion_clear H
       | |- pvalue ?env _ T _ => constructor
       | |- pvalue ?env _ F _ => constructor
       | |- _ => subst           
      end) || s); trivial.

  Lemma andb_pcorrect env bdd (Hwf: wf bdd) n a b ab bdd' :
    andb bdd n a b = Some (ab, bdd') ->
    forall va, pvalue env bdd a va -> 
          forall vb, pvalue env bdd b vb -> 
                pvalue env bdd' ab (va && vb)%bool * incr bdd bdd'.
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
        eapply binop_pcorrect_eq; eauto.  
      + t s; eauto using binop_pcorrect_lt.        
      + t s; eauto using binop_pcorrect_gt. 
  Qed.
  
  
  Lemma orb_pcorrect env bdd (Hwf: wf bdd) n a b ab bdd' :
    orb bdd n a b = Some (ab, bdd') ->
    forall va, pvalue env bdd a va -> 
          forall vb, pvalue env bdd b vb -> 
                (pvalue env bdd' ab (va || vb)%bool * incr bdd bdd').
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
        eauto using binop_pcorrect_eq. 
      + t s; eauto using binop_pcorrect_lt.        
      + t s; eauto using binop_pcorrect_gt.
  Qed.  
  
  Lemma negb_pcorrect env bdd (Hwf: wf bdd) n a a' bdd' :
    negb bdd n a = Some (a', bdd') ->
    forall va, pvalue env bdd a va -> 
          (pvalue env bdd' a' (Datatypes.negb va)%bool * incr bdd bdd').
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
      destruct (pvalue_inv_env _ _ _ _ _ _ _ I Hva) as [vxa Hxa]. 

      destruct (pvalue_N_inversion env bdd a va Hva _ _ _ I _ Hxa) as [vla [vha [[Hla Hha] Hwa]]].
      destruct (IHn _ Hwf _ _ _ I1 _ Hla) as [Hvx Hincr]; clear I1. 
      refine (let (Hvx1,Hincr2) := IHn x0 (_ : wf x0) _ _ _ I0 
                                       _ (_: pvalue env _ ha vha) 
              in _
             ); eauto.
      pose proof (pvalue_inj _ _ _ _ Hva _ Hwa); subst. 
      refine (let (Hab, Hincr2) := mk_node_pcorrect (_ : wf x2) H _ _ _ _ _ _ in _
             ); eauto. 
      split; destruct (vxa); eauto. 
  Qed.
  
  Lemma xorb_pcorrect env bdd (Hwf: wf bdd) n a b ab bdd' :
    xorb bdd n a b = Some (ab, bdd') ->
    forall va, pvalue env bdd a va -> 
          forall vb, pvalue env bdd b vb -> 
                (pvalue env bdd' ab (Datatypes.xorb va vb)%bool * incr bdd bdd').
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
      destruct a as [ | | a]; destruct b as [ | | b]; simpl in *; t s; eauto using negb_pcorrect. 
      
      destruct x as [[la xa] ha]. destruct x0 as [[lb xb] hb]. 
      destruct (NPeano.Nat.compare xa xb) eqn: Heq.
      + apply nat_compare_eq in Heq; subst; t s. 
        eauto using binop_pcorrect_eq. 
      + t s; eauto using binop_pcorrect_lt. 
      + t s; eauto using binop_pcorrect_gt. 
  Qed.
   
  Lemma mk_var_pcorrect' env bdd (Hwf: wf bdd) v ptr bdd' :
    mk_var bdd v = (ptr, bdd') -> 
    forall r, List.nth_error env v = Some r -> 
    pvalue env bdd' ptr r * incr bdd bdd'. 
  Proof. 
    unfold mk_var. intros. 
    eapply (@mk_node_pcorrect env) in H; eauto.  
    destruct (r); apply H. 
  Qed. 


  Lemma mk_var_pcorrect bdd (Hwf: wf bdd) bdd' env ptr e: 
    mk_var bdd (Datatypes.length env) = (ptr, bdd') -> 
    pvalue (List.app env [e]) bdd' ptr e. 
  Proof.   
    intros. 
    pose proof (mk_var_pcorrect' (List.app env [e]) _ _ _ _ _ H e).  
    rewrite list_nth_error_length in X. specialize (X refl_equal). intuition.  
  Qed. 

  Lemma ite_pcorrect bdd (Hwf: wf bdd) bdd' n env c l r ptr: 
    ite bdd n c l r = Some (ptr, bdd') -> 
    forall vc, pvalue env bdd c vc -> 
          forall vl, pvalue env bdd l vl -> 
                forall vr, pvalue env bdd r vr -> 
                      (pvalue env bdd' ptr  (if vc then vl else vr) * incr bdd bdd'). 
  Proof. 
    unfold ite.
    intros H. simpl_do. intros. 
    eapply andb_pcorrect in H0; eauto. destruct H0.      
    eapply negb_pcorrect in H; eauto. destruct H.   
    eapply andb_pcorrect in H1; eauto. destruct H1. 
    eapply orb_pcorrect in H3; eauto. destruct H3. 
    simpl in *. 
    destruct vc; simpl in p2; split; eauto.   
    rewrite Bool.orb_comm in p2. apply p2. 
  Qed. 
End pvalue. 

Lemma mk_var_incr bdd (Hwf: wf bdd) bdd' n ptr: 
  mk_var bdd n = (ptr, bdd') -> 
  incr bdd bdd'. 
Proof. 
  intros. 
  eapply (mk_var_correct (fun _ => false)) in H. 
  destruct H. auto. 
  auto. 
Qed.   

Lemma mk_var_path bdd bdd' (Hwf: wf bdd) n ptr: mk_var bdd n = (ptr, bdd') -> 
                                  path bdd' ptr. 
Proof. 
  intros H. eapply (mk_var_correct (fun _ => false)) in H; auto.
  destruct H as [Hv Hincr]. 
  apply path_of_value in Hv. auto. 
Qed. 



Lemma wf_empty : wf empty. 
Proof. 
  constructor; simpl; intros.
  - split; intro H. 
    rewrite NMapFacts.empty_o in H. discriminate. 
    rewrite PMap.gempty in H. discriminate. 
  - rewrite PMap.gempty in H. discriminate.  
  - exfalso. zify; omega. 
  - exfalso. zify; omega. 
  - inversion H. simpl in H1. rewrite PMap.gempty in H1. clear - H1; discriminate. 
Qed. 