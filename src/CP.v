Require Import Common DList Core ZArith. 
Require BDD.

(* In this compilation pass, we implement boolean simplification using BDDs. *)

Section t. 

  Variable Phi : state.   
  Variable Var : type -> Type.
  
  (* Maybe we have a pointer *)
  Definition sval := option BDD.expr. 

  Notation V := (fun t => Var t * sval)%type.   
  
  (* The symbolic values *)
  Inductive bexpr :=
  | Lift : BDD.expr  -> bexpr
  | Ite : forall (c l r : BDD.expr), bexpr
  | And : forall (a b : BDD.expr), bexpr
  | Or : forall (a b : BDD.expr), bexpr
  | Xor : forall (a b : BDD.expr), bexpr
  | Not : forall (a : BDD.expr), bexpr.
    
  (* bang := lift Lift *)
  Notation bang x := (do e <- x; (Some (Lift e))). 
  Notation "!!" := (None). 

  Notation bop op dl:= 
  (let a := DList.hd dl in 
   let b := DList.hd (DList.tl dl) in 
     do a <- (snd a);            (* take the symbolic value of a *)
     do b <- (snd b);            (* take the symbolic value of b *)
     Some (op a b)).            (* apply the operation on the symbolic values *)

  Require Import RTL. 
  Definition cp_expr t (e : expr Phi V t) : (expr Phi Var t) * (option bexpr). 
  refine (match e with
            | Evar t x => 
                match t as ty return V ty -> (expr Phi Var ty) * (option bexpr) with 
                  | Tbool => fun y => (Evar (fst y), bang (snd y)) 
                  | t => fun y  => (Evar (fst y), !!) end x
            | Eread t v => (Eread v, !!)
            | Eread_rf n t v adr => (Eread_rf v (fst adr), !!)
            | Ebuiltin tys res f args  => 
                (Ebuiltin f (DList.map (fun _ x => fst x) args), _)           
            | Econstant t x => 
                match t as ty return constant ty -> (expr Phi Var ty * option bexpr) with
                  | Tbool => fun c => if ( c : bool)
                                    then (Econstant c, Some (Lift BDD.T))
                                    else (Econstant c, Some (Lift BDD.F))
                  | t => fun c => (Econstant c, !!) end x
            | Emux ty c l r => 
                (_ ,
                 match ty as t return V t -> V t  -> option bexpr with 
                   | Tbool => fun l r =>  
                               (do c <- (snd c);
                                do l <- (snd l);
                                do r <- (snd r);
                                Some (Ite c l r))
                   | _ => fun _ _ => !! end l r)
            | Efst l t v => (Efst (fst v) , !!)
            | Esnd l t v => (Esnd (fst v) , !!)
            | Enth l t m v => (Enth m (fst v), !!)
            | Etuple l dl => (Etuple (DList.map (fun _ x => fst x) dl), !!)
          end). 
  refine (match f in builtin tys res return DList.T V tys -> option bexpr with
            | BI_andb => fun dl =>  bop And dl
            | BI_orb  => fun dl =>  bop Or  dl
            | BI_xorb => fun dl =>  bop Xor dl
            | BI_negb => fun dl =>  do e <- (snd (DList.hd dl)); Some (Not e)
            | _ => fun _ => !!
          end args); simpl.
  refine (match snd c with 
                   | Some BDD.T => (Evar (fst l))
                   | Some BDD.F => (Evar (fst r))
                   |  _ => Emux (fst c) (fst l) (fst r) end).  
  Defined. 

  Record Env := mk
    {
      Ebdd : BDD.BDD;
      Eknown: list (BDD.expr * Var Tbool);
      Enext: nat
    }. 

  Definition empty : Env := mk BDD.empty [] 20. 
  
  Definition add_bdd (Gamma: Env) (b:bexpr ): option (BDD.expr * Env) :=  
    match b with
      | Lift x => Some (x, Gamma)
      | Ite c l r => 
          do v, bdd <- BDD.ite (Ebdd Gamma) (Enext Gamma) c l r;
          Some (v, mk bdd (Eknown Gamma) (Enext Gamma))
      | And a b => 
          do  r,bdd <- BDD.andb (Ebdd Gamma) (Enext Gamma) a b;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
      | Or a b => 
          do  r,bdd <- BDD.orb (Ebdd Gamma) (Enext Gamma) a b;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
      | Xor a b => 
          do r,bdd  <- BDD.xorb (Ebdd Gamma) (Enext Gamma) a b;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
      | Not a => 
          do r,bdd <- BDD.negb (Ebdd Gamma) (Enext Gamma) a;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
    end. 

  Definition lookup (Gamma: Env) (b: BDD.expr) : option (Var Tbool) :=
    BDD.assoc BDD.expr_eqb b (Eknown Gamma). 

  Definition add_env (Gamma: Env) (v:Var Tbool) (b:BDD.expr): Env :=
    mk (Ebdd Gamma) ((b,v) :: Eknown Gamma) (Enext Gamma). 
  
  Definition incr Gamma :=
    let n := (Enext Gamma) in 
    let (r, bdd) := BDD.mk_var (Ebdd Gamma) n in
      (r, mk bdd (Eknown Gamma) (S n)). 

  (* Unfortunately, multiple reads from the same state elements cannot be shared *)
  Fixpoint cp_telescope {A} (Gamma: Env) (T : telescope Phi V A) : telescope Phi Var A :=
    match T with
      | & x => & x
      | telescope_bind arg b cont => 
        let (e,sv) := cp_expr arg b in 
        match arg return 
              (Var arg * sval -> telescope Phi V A) -> 
              expr Phi Var arg -> telescope Phi Var A 
        with 
          | Tbool => 
            match sv with 
              | None => 
                fun cont e => 
                  (
                    k :- e; 
                    let (ptr, Gamma) := incr Gamma in 
                    let Gamma := add_env Gamma k ptr in (* we add the mapping ptr ~> k in the environment *)
                    cp_telescope Gamma (cont (k, Some ptr))
                  )
              | Some v => 
                fun cont e =>  
                  match add_bdd Gamma v with 
                    | Some (ptr, Gamma) =>
                      (* the symbolic value correspond to a pointer in the bdd *)
                      match lookup Gamma ptr with
                        | None => (* this pointer does not correspond to a
                                 value. We bind this value, and add it
                                 to the environment*)                          
                          (k :- e;
                           let Gamma := add_env Gamma k ptr in 
                           cp_telescope  Gamma (cont (k, Some ptr)))
                        | Some old => 
                          (* This pointer was already mapped to a value. No need to bind a new value *)
                          cp_telescope Gamma (cont (old, (Some ptr))) 
                      end
                    | None => 
                      (* adding to the bdd failed. This should not happen, but is safe *)
                      k :- e; cp_telescope Gamma (cont (k,None))
                  end
            end
          | _ => fun cont e => 
                  k :- e; cp_telescope Gamma (cont (k, None))
        end cont e
    end.  

  Definition cp_effects (eff: effects Phi V) : effects Phi Var :=
    DList.map
         (fun (a : sync) (x : (option ∘ effect V) a) =>
            match x with
              | Some x0 =>
                  match x0 in (effect _ s) return ((option ∘ effect Var) s) with
                    | effect_reg_write t x1 x2 =>
                        Some (effect_reg_write Var t (fst x1) (fst x2))
                    | effect_regfile_write n t x1 x2 x3 =>
                        Some (effect_regfile_write Var n t (fst x1) (fst x2) (fst x3))
                  end
              | None => None
            end) eff. 
  
  
  Definition cp_block  t (b : block Phi V t) : block Phi Var t :=    
    (* let b := ( _ :- @Econstant  _ _ Tbool true ; *)
    (*            _ :- @Econstant  _ _ Tbool false ; *)
    (*            b) in  *)
    k :-- cp_telescope empty b;
    match k with (v,g,e) =>
                   & (fst v, fst g, cp_effects  e)
    end. 
End t.   

Notation V := (fun t => eval_type t * sval)%type.   

Definition lift (env : list (BDD.expr * bool)) : BDD.var -> bool :=
  fun n => 
    match List.nth_error env n with 
      | None => true
      | Some (e,b) => b
    end. 


Definition interp (E: Env eval_type) v := 
  BDD.interp (lift (Eknown _ E)) (Ebdd _ E) (S (Enext _ E)) v. 


Definition eval_bexpr (E: Env eval_type) (b: bexpr) : option (bool) :=
  match b with
    | Lift x => interp E x 
    | Ite c l r => do c <- interp E c; 
                  do l <- interp E l;
                  do r <- interp E r;
                  Some (if c then l else r)
    | And a b => do a <- interp E a; 
                do b <- interp E b; 
                Some (a && b)%bool
    | Or a b => do a <- interp E a; 
               do b <- interp E b; 
               Some (a || b)%bool
    | Xor a b => do a <- interp E a; 
                do b <- interp E b; 
                Some (xorb a b)%bool
    | Not a => do a <- interp E a; 
              Some (negb a)%bool
  end. 

Notation "G |= x -- y" := (In _ _ _ x y G) (no associativity, at level 71). 

Definition value (E: Env eval_type) sv x := match sv with 
                                                None => False
                                              | Some v => BDD.value (lift (Eknown _ E)) (Ebdd _ E) v x
                                            end. 


  
Class inv (G: Gamma eval_type V) (E: Env eval_type) :=
  {
    inv_1 : forall t (x : eval_type t) y, G |= x -- y -> x = fst y;
    inv_2 : forall (x: eval_type Tbool) y, G |= x -- y -> 
                                      value E (snd y) x; 
    inv_bdd_wf : BDD.wf (lift  (Eknown _ E)) (Ebdd _ E); 
    inv_next : (Enext _ E) = BDD.wf_depth _ _ inv_bdd_wf
  }. 
    
Lemma inv_interp {G E} {Hinv : inv G E} (x: eval_type Tbool) y e:
  forall (H: G |= x -- (y, Some e)),  
    interp E e = Some x. 
Proof. 
  intros. 
  unfold interp. 
  rewrite inv_next. apply BDD.interp_S.  apply BDD.wf_value_interp.  
  apply inv_2 in H. simpl in H. apply H. 
Qed. 
 
Notation R := (fun G t x y => In _ _ t x y G).  

(** The dependent type swiss-knife. *)
Ltac t :=  subst; repeat match goal with 
                       H : existT _ _ _ = existT _ _ _ |- _ => 
                         apply Eqdep.EqdepTheory.inj_pair2 in H
                   |   H : context [eq_rect ?t _ ?x ?t ?eq_refl] |- _ => 
                         rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H
                   |   H : context [eq_rect ?t _ ?x ?t ?H'] |- _ => 
                         rewrite (Eqdep.EqdepTheory.UIP_refl _ _ H') in H;
                         rewrite <- Eqdep.EqdepTheory.eq_rect_eq in H
                   |   H : existT _ ?t1 ?x1 = existT _ ?t2 ?x2 |- _ => 
                         let H' := fresh "H'" in 
                           apply EqdepFacts.eq_sigT_sig_eq in H; destruct H as [H H']; subst
                         end; subst.

(* Lemma Gamma_inv_cons_bool G env e f sv :  *)
(*   Gamma_inv G env -> *)
(*   value env sv e ->  *)
(*   forall (heq: e = f),  *)
(*     Gamma_inv (cons eval_type V Tbool e (f,sv) G) env.  *)
(* Proof.  *)
(*   intros. constructor.  *)
(*   - intros. inversion H0; t. reflexivity. apply Gamma_inv_1. eauto.  *)
(*   - intros. admit.  *)
(* Qed.  *)

(* Lemma Gamma_inv_cons G env t e f:  *)
(*   Gamma_inv G env -> *)
(*   t <> Tbool ->  *)
(*   forall  Heq : e = f,  *)
(*     Gamma_inv (cons eval_type V t e (f,None) G) env.  *)
(* Proof.  *)
(*   intros. constructor.  *)
(*   - intros. inversion H0; t. reflexivity. apply Gamma_inv_1. eauto.  *)
(*   - intros. admit.  *)
(* Qed.         *)

Lemma cp_expr_correct Phi st : 
  forall t e1 r1, 
    eval_expr Phi st t e1 = r1 ->
    forall G (env : Env eval_type) e2,
      expr_equiv _ _ Phi (R G) t e1 e2 ->     
      inv G env
      -> match t as ty return eval_type ty -> Prop
        with 
          | Tbool => 
            match snd (cp_expr Phi _ t  e2) 
            with
              | Some sv => fun r1 => eval_bexpr env sv  = Some r1
              | None => fun _ => True
            end
          | _ => fun _ => True
        end r1.
Proof. 
  destruct 1; inversion 1; t;  try solve [destruct t; simpl; auto]; intros. 
  - simpl. destruct t; trivial; clear H. 
    Require Import Equality. 

    Ltac d :=
      repeat match goal with 
        | H : DList.pointwise _ (?t :: ?q) _ _ |- _ => 
          apply DList.inversion_pointwise in H; 
            destruct H
        | H : DList.pointwise _  [] _ _ |- _ => clear H
        | x :( _ * sval)%type |- _ => destruct x as [ ? [? | ]]
      end. 

    dependent destruction f; simpl; repeat DList.inversion; d; simpl; trivial;  
    repeat match goal with 
      | H :    ?G |= ?x -- (?v, Some ?e) |- context [?e] => 
        rewrite (inv_interp _ _ _ H)
    end; simpl; try reflexivity. 
  - destruct t; trivial. destruct c; reflexivity.   
  - destruct t; trivial; d;  simpl; trivial.  
    repeat match goal with 
             | H :    ?G |= ?x -- (?v, Some ?e) |- context [?e] => 
               rewrite (inv_interp _ _ _ H)
           end; simpl; try reflexivity. 
  - trivial. 
  - trivial. 
Qed. 


Lemma cp_effects_correct (Phi : state) st Delta G e  (Hg : inv G e):
  forall e1 e2 
  (H : effects_equiv eval_type V Phi (RTL.R eval_type V G) e1 e2), 
   eval_effects Phi st e1 Delta =
   eval_effects Phi st (cp_effects Phi eval_type e2) Delta. 
Proof. 
  intros e1 e2 H.
  apply DList.map3_map.   
  eapply DList.pointwise_map; [| apply H];
  clear H; simpl in *; intros. 
  inversion H;  t; unfold RTL.R in *; 
  repeat (match goal with 
            | |- ?x = ?x  => reflexivity
            | |- context [match ?x with _=> _ end] => 
              case_eq x; intros
            | H' : In _ _ _ ?x ?y _ |- _ => 
              rewrite (inv_1 _ _ _ H')
            | H : context [fst ?x] |- _ => progress (simpl in H)
            | H : ?x = ?x |- _ => clear H
            | H : ?y = ?x, H' : ?x = ?y |- _ => clear H'
            | x : (_ * _)%type |- _ =>  destruct x; simpl; subst
          end); simpl. 
Qed. 
Lemma inv_cons_None G E t e f: 
  inv G E -> 
  e = f -> 
  inv (cons eval_type V t e (f, None) G) E. 
Proof. 
  intros Hinv Heq; subst. 
  econstructor. 
  + intros.  
    inversion H; t.  reflexivity. 
    apply Hinv; auto. 
    
  + intros. admit. 
  + apply Hinv. 
Qed. 

Lemma cp_expr_correct_2 Phi st G env (Hg : inv G env) t:
  forall e1 e2, expr_equiv eval_type V Phi (RTL.R eval_type V G) t e1 e2 ->
           forall svo e, cp_expr Phi eval_type t e2 = (e,svo) ->
                           eval_expr Phi st t e1 = eval_expr Phi st t e. 
Proof.
  Ltac crush :=
    repeat (match goal with 
      | H: (_,_) = (_,_) |- _ => injection H; clear H; intros; subst
      | Hg : inv _ _ ,  H : In _ _ _ ?x ?y _ |- context [?x] =>
        rewrite (inv_1 _ _ _ H)
      | H : DList.T [] |- _ => DList.inversion 
      | H : DList.T (_ :: _) |- _  => DList.inversion 
      | H : DList.pointwise _ ( _ :: _) _ _ |- _ => apply DList.inversion_pointwise in H; destruct H
    end); try reflexivity; try f_equal. 
  intros e1. destruct e1; intros e2 H; inversion H; t; simpl; intros; unfold RTL.R in *; crush.
  
  - simpl. f_equal. 
    clear H b. 
    induction args; repeat DList.inversion;simpl; intuition. 
    + crush.  eauto.  
  -  destruct ty; crush. destruct c; crush. 
  - clear H.  
    destruct c2. simpl.  destruct s; simpl. destruct e3; simpl.
    
    Ltac save :=
      repeat match goal with 
        |  H : _ |= _ -- _ |- _ =>
           pose proof (inv_1 _ _ _ H);
           pose proof (inv_interp _ _ _ H);
                    clear H
      end. 
    save. simpl in *; subst. compute in H0. injection H0; intros; subst. reflexivity. 
    save. simpl in *; subst. compute in H0. injection H0; intros; subst. reflexivity.
    reflexivity. 
    reflexivity. 
  - simpl. clear H. 
    induction l; repeat DList.inversion;simpl; intuition. 
    + crush; eauto. 

Qed. 


Lemma cp_telescope_correct (Phi: state) st t  Delta: 
     forall (b : RTL.block Phi eval_type t)
       (b': RTL.block Phi V t)
       (G : Gamma eval_type V),
       block_equiv eval_type V Phi t G b b' ->
       forall e,
       inv  G e
     ->
   eval_telescope Phi st
     (fun x : eval_type t * bool * effects Phi eval_type =>
      let (y, e0) := x in
      let (p, g) := y in check g; Some (p, eval_effects Phi st e0 Delta)) b =
   eval_telescope Phi st
     (fun x : eval_type t * bool * effects Phi eval_type =>
      let (y, e0) := x in
      let (p, g) := y in check g; Some (p, eval_effects Phi st e0 Delta))
     (k :-- cp_telescope Phi eval_type e b';
      (let (p, e0) := k in
       let (v, g) := p in & (fst v, fst g, cp_effects Phi eval_type e0))). 
Proof. 
  Ltac crush ::=
    repeat match goal with 
             | H: (_,_) = (_,_) |- _ => injection H; clear H; intros; subst
             | H : In _ _ _ ?x ?y _ |- context [?x] =>
               rewrite (inv_1 _ _ _ H)
             | H : DList.T [] |- _ => DList.inversion 
             | H : DList.T (_ :: _) |- _  => DList.inversion 
             | H : DList.pointwise _ ( _ :: _) _ _ |- _ => apply DList.inversion_pointwise in H; destruct H
             | |- Some _ = Some _ => f_equal
             | |- (_,_) = (_,_) => f_equal
             | |- context [eval_type _] => simpl eval_type
           end; try reflexivity. 
  
  induction 1 as [G v1 v2 g1 g2 e1 e2 Hv Hg He| G a e1 e2 k1 k2 He Hk IH]; simpl; intros E INV. 
  - crush.
    match goal with 
      |- context [(if ?x then _ else _) = (if ?y then _ else _)] => 
      let H := fresh in 
      assert (H : x = y)  by reflexivity; 
      subst; clear H; destruct x
    end; f_equal; f_equal. eapply cp_effects_correct; eauto.   
  - destruct (cp_expr Phi eval_type a e2) as [binding [sv | ]]eqn: Heq; destruct a; 
    try (apply IH; apply inv_cons_None; eauto using cp_expr_correct_2 ).
    
    {
       destruct (add_bdd eval_type E sv) as [[ptr E2] | ]eqn:Heq2; [|apply IH]. 
       destruct (lookup eval_type E2 ptr) as [old | ] eqn:Heq3; apply IH.
       clear IH. 
       pose proof (cp_expr_correct_2 _ st _ _ INV _ _ _ He _ _ Heq). 
       rewrite H. 
       pose proof (cp_expr_correct _ _ _ _ _ H _ _ _ He INV). simpl in H0.
       rewrite Heq in H0. simpl in H0. 
       Lemma inv_cons_lookup_Some G E (INV : inv G E) E2 sv ptr old X:
         add_bdd eval_type E sv = Some (ptr, E2) -> 
         lookup eval_type E2 ptr = Some old -> 
         eval_bexpr E sv = Some X -> 
         inv (cons eval_type V B X (old, Some ptr) G) E2. 
       Proof. 
       Admitted. 
       eapply inv_cons_lookup_Some; eauto. 
       pose proof (cp_expr_correct_2 _ st _ _ INV _ _ _ He _ _ Heq). 
       rewrite H. 
       pose proof (cp_expr_correct _ _ _ _ _ H _ _ _ He INV). simpl in H0.
       rewrite Heq in H0. simpl in H0.
       Lemma inv_cons_lookup_None G E (INV : inv G E) E2 sv ptr X:
         add_bdd eval_type E sv = Some (ptr, E2) -> 
         lookup eval_type E2 ptr = None -> 
         eval_bexpr E sv = Some X -> 
         inv (cons eval_type V B X (X, Some ptr) G) (add_env eval_type E2 X ptr). 
       Proof. 
       Admitted. 
       eapply inv_cons_lookup_None; eauto. 
       apply inv_cons_None; eauto using cp_expr_correct_2. 
    }
    {
      destruct (incr eval_type E) as [ptr E'] eqn: Hincr.
      apply IH; clear IH. 
      eapply cp_expr_correct_2 in Heq; eauto.  
      rewrite Heq; clear Heq.  
      generalize (eval_expr Phi st B binding). 
      intros e. 
      Lemma inv_cons_incr G E (INV : inv G E) e ptr E2: 
        incr eval_type E = (ptr, E2) -> 
        inv (cons eval_type V B e (e, Some ptr) G) (add_env eval_type E2 e ptr).
      Proof. 
      Admitted. 
      eapply inv_cons_incr; eauto. 
    }
Qed.     

Lemma Gamma_inv_empty : inv  (nil _ _ ) (empty eval_type). 
Proof. 
Admitted. 

Theorem cp_correct Phi st t (b : Block Phi t) Delta : WF Phi t b -> 
  eval_block Phi st t (b _) Delta = eval_block Phi st t (cp_block Phi eval_type t (b _)) Delta. 
Proof. 
  intros.
  eapply cp_telescope_correct; eauto using Gamma_inv_empty.
Qed. 
  

Definition Compile Phi t (b : Block Phi t) : Block Phi t :=  
  fun V => cp_block Phi V t (b _). 

Theorem Compile_correct Phi t b (Hwf : WF Phi t b): forall st Delta,
  Eval Phi st t (Compile Phi t b) Delta =  Eval Phi st t b Delta. 
Proof. 
  unfold Eval. intros. unfold Compile. symmetry. apply cp_correct. auto. 
Qed. 

Print Assumptions Compile_correct. 