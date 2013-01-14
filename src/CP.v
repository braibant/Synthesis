Require Import Common DList Core ZArith. 
Require BDD Seq.

(** In this compilation pass, we implement boolean simplification
    using BDDs.  Every boolean value is tagged with an abstraction of
    its runtime value, and when two declared variables have equivalent
    values, we do not introduce a binder for the second one. This
    transformation is similar to CSE, except that we use semantic
    common sub-expression elimination. *)

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
  Definition cp_expr t (e : expr Phi V t) : (expr Phi Var t) * (option bexpr) :=
    match e with
            | Einput t v => (Einput _ _ _ v, !!)
            | Evar t x => 
                match t as ty return V ty -> (expr Phi Var ty) * (option bexpr) with
                  | Tbool => fun y => (Evar (fst y), bang (snd y))
                  | t => fun y  => (Evar (fst y), !!) end x
            | Eread t v =>  (Eread v, !!)
            | Eread_rf n t v adr => (Eread_rf v (fst adr), !!) 
            | Eandb a b => (Eandb _ _ (fst a) (fst b), 
                           (do a <- snd a; do b <- snd b; Some (And a b)))
            | Eorb a b =>  (Eorb  _ _ (fst a) (fst b),
                           do a <- snd a; do b <- snd b; Some (Or a b))                            
            | Exorb a b => (Exorb _ _ (fst a) (fst b), 
                           do a <- snd a; do b <- snd b; Some (Xor a b))
            | Enegb a   => (Enegb _ _ (fst a), 
                           do a <- snd a; Some (Not a))
            | Eeq t a b => (Eeq _ _ t (fst a) (fst b), !!)
            | Elt n a b => (Elt _ _ n (fst a) (fst b), !!)
            | Eadd n a b => (Eadd _ _ n (fst a) (fst b), !!)
            | Esub n a b => (Esub _ _ n (fst a) (fst b), !!)
            | Elow n m a => (Elow _ _ n m (fst a), !!)
            | Ehigh n m a => (Ehigh _ _ n m (fst a), !!)
            | EcombineLH n m a b => (EcombineLH _ _ n m (fst a) (fst b), !!)
            | Econstant t x => 
                match t as ty return constant ty -> (expr Phi Var ty * option bexpr) with
                  | Tbool => fun c => if ( c : bool)
                                    then (Econstant c, Some (Lift BDD.T))
                                    else (Econstant c, Some (Lift BDD.F))
                  | t => fun c => (Econstant c, !!) end x
            | Emux ty c l r => 
                (match snd c with 
                   | Some BDD.T => (Evar (fst l))
                   | Some BDD.F => (Evar (fst r))
                   |  _ => Emux (fst c) (fst l) (fst r) end
                 ,
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
          end. 

  Record Env := mk
    {
      Ebdd : BDD.BDD;
      
      (* An association list that maps pointers in the BDD to variables *)
      Eassoc: list (BDD.expr * Var Tbool);
      
      (* The denotation of the variables of the bdd (i.e, the uninterpreted booleans) *)
      Evalues: list (Var Tbool); 
      
      Enext: nat
    }. 

  Definition empty : Env := mk BDD.empty [] [] 0. 
  
  Definition add_bdd (Gamma: Env) (b:bexpr ): option (BDD.expr * Env) :=  
    match b with
      | Lift x => Some (x, Gamma)
      | Ite c l r => 
          do v, bdd <- BDD.ite (Ebdd Gamma) (Enext Gamma) c l r;
          Some (v, mk bdd (Eassoc Gamma) (Evalues Gamma) (Enext Gamma))
      | And a b => 
          do  r,bdd <- BDD.andb (Ebdd Gamma) (Enext Gamma) a b;
          Some (r, mk bdd (Eassoc Gamma) (Evalues Gamma) (Enext Gamma))
      | Or a b => 
          do  r,bdd <- BDD.orb (Ebdd Gamma) (Enext Gamma) a b;
          Some (r, mk bdd (Eassoc Gamma) (Evalues Gamma) (Enext Gamma))
      | Xor a b => 
          do r,bdd  <- BDD.xorb (Ebdd Gamma) (Enext Gamma) a b;
          Some (r, mk bdd (Eassoc Gamma) (Evalues Gamma) (Enext Gamma))
      | Not a => 
          do r,bdd <- BDD.negb (Ebdd Gamma) (Enext Gamma) a;
          Some (r, mk bdd (Eassoc Gamma) (Evalues Gamma) (Enext Gamma))
    end. 

  Definition lookup (Gamma: Env) (b: BDD.expr) : option (Var Tbool) :=
    BDD.assoc BDD.expr_eqb b (Eassoc Gamma). 

  Definition incr Gamma v :=
    let n := (Enext Gamma) in 
    let (r, bdd) := BDD.mk_var (Ebdd Gamma) n in
      (r, mk bdd (Eassoc Gamma) (Evalues Gamma ++ [v]) (S n)). 

  Definition add_env (Gamma: Env) (v:Var Tbool) (b:BDD.expr): Env :=
    mk (Ebdd Gamma) (List.app (Eassoc Gamma) [(b,v)]) (Evalues Gamma) (Enext Gamma). 
  
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
                    let (ptr, Gamma) := incr Gamma k in 
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
         (fun (a : mem) (x : (option ∘ effect V) a) =>
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
Arguments Ebdd {Var} e. 
Arguments Evalues {Var} e. 
Arguments Eassoc {Var} e. 
Arguments Enext {Var} e. 

Notation V := (fun t => eval_type t * sval)%type.   

  
Definition value (E: Env eval_type) (e : BDD.expr) v :=
  BDD.pvalue  (Evalues E) (Ebdd E) e v. 

Inductive bvalue (E: Env eval_type) : bexpr -> bool -> Type :=
|bvalue_Lift: forall x vx, value E x vx -> 
                     bvalue E (Lift x) vx 
|bvalue_Ite: forall c vc, value E c vc -> 
              forall l vl, value E l vl -> 
              forall r vr, value E r vr -> 
                     bvalue E (Ite c l r) (if vc then vl else vr)
|bvalue_And: forall a va, value E a va -> 
            forall b vb, value E b vb -> 
                   bvalue E (And a b) (va && vb)
|bvalue_Or: forall a va, value E a va -> 
           forall b vb, value E b vb -> 
                   bvalue E (Or a b) (va || vb)
|bvalue_XOr: forall a va, value E a va -> 
                     forall b vb, value E b vb -> 
                  bvalue E (Xor a b) (xorb va vb)                         
|bvalue_Not: forall a va, value E a va -> 
                      bvalue E (Not a) (negb va). 
    
Notation "G |= x -- y" := (In _ _ _ x y G) (no associativity, at level 71). 

(* Recall that V t is defined as  eval_type t * sval, and sval = option BDD.expr. 
   We have G |= x -- (v, Some e) when x = v and BDD.value e v 
 *)

Record inv (G: Gamma eval_type V) (E: Env eval_type) :=
  {
    inv_1 : forall t (x : eval_type t) y, G |= x -- y -> x = fst y;
    inv_2 : forall (x: eval_type Tbool) x' e , G |= x -- (x', Some e) -> 
                                      value E e x; 
    inv_path : forall  (x: eval_type B) x' e, G |= x -- (x',Some e) -> 
                        BDD.path (Ebdd E) e;
    inv_bdd_wf : BDD.wf  (Ebdd E); 
    inv_next_2 : (Enext E) = List.length (Evalues E) ;
    inv_assoc : forall x (y: BDD.expr), Seq.In (y,x) (Eassoc E) -> G |= x -- (x,Some y)            
  }. 

Arguments inv_1 {G E} _ t x y _.
Arguments inv_2 {G E} _ x x' e _.
Arguments inv_path {G E} _ x x' e _.
Arguments inv_bdd_wf {G E} _.
Arguments inv_next_2 {G E} _.
Arguments inv_assoc {G E} _ x y _.

Notation R := (fun G t x y => In _ _ t x y G).  

Ltac d := 
  repeat 
    match goal with 
          | x: (eval_type _ * sval)%type, 
               H: _ |= _ -- ?x' |- _ => constr_eq x x'; destruct x
          | H: context [snd ?x] |- _ => simpl in H
          | H: ?x = Some _ |- _ => subst
        end. 

Hint Unfold value.

Lemma cp_expr_correct Phi st : 
  forall e1 r1, 
    eval_expr Phi st B e1 = r1 ->
    forall G (env : Env eval_type) e2,
      expr_equiv _ _ Phi (R G) B e1 e2 ->     
      inv G env -> 
      forall sv, snd (cp_expr Phi _ B  e2) = Some sv -> 
            bvalue env sv r1. 
Proof. 
  destruct 1; inversion 1; injectT;  try solve [destruct t; simpl; auto]; intros INV sv; simpl; try discriminate.  
  - intros; simpl_do. d. constructor; eapply inv_2; eassumption. 
  - intros; simpl_do. d. constructor; eapply inv_2; eassumption.
  - intros; simpl_do. d. constructor; eapply inv_2; eassumption.
  - intros; simpl_do. d. constructor; eapply inv_2; eassumption. 
  - destruct c; simpl; intros H; inject H; eauto. constructor. eauto. constructor. eauto. 
  - intros; simpl_do. d. constructor; eapply inv_2; eassumption. 
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
  inversion X; injectT; unfold RTL.R in *; 
  repeat (match goal with 
            | |- ?x = ?x  => reflexivity
            | |- context [match ?x with _=> _ end] => 
              case_eq x; intros
            | H' : In _ _ _ ?x ?y _ |- _ => 
              rewrite (inv_1 Hg _ _ _ H')
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
  + intros ty x y.  inversion 1; injectT.  reflexivity. 
    apply Hinv; auto. 
    
  + intros x x' e H. inversion H; injectT. discriminate. eapply inv_2; eassumption.  
  + intros x x' e H. inversion H; injectT. congruence.  eapply inv_path; eauto.  
  + apply Hinv. 
  + intros. apply Hinv.
  + intros. apply In_skip. eapply inv_assoc; eauto.  
Qed. 

Lemma cp_expr_correct_2 Phi st G env (Hg : inv G env) t:
  forall e1 e2, expr_equiv eval_type V Phi (RTL.R eval_type V G) t e1 e2 ->
           forall svo e, cp_expr Phi eval_type t e2 = (e,svo) ->
                           eval_expr Phi st t e1 = eval_expr Phi st t e. 
Proof.
  Ltac crush :=
    repeat (match goal with 
      | H: (_,_) = (_,_) |- _ => inject H
      | Hg : inv _ _ ,  H : In _ _ _ ?x ?y _ |- context [?x] =>
        rewrite (inv_1 Hg _ _ _ H)
      | H : DList.T [] |- _ => DList.inversion 
      | H : DList.T (_ :: _) |- _  => DList.inversion 
      | H : DList.pointwise _ ( _ :: _) _ _ |- _ => apply DList.inversion_pointwise in H; destruct H
    end); try reflexivity; try f_equal. 
  intros e1. destruct e1; intros e2 H; inversion H; injectT; simpl; intros; unfold RTL.R in *; crush.
  - destruct ty; crush. destruct c; crush. 
  - clear H.  
    destruct c2. simpl.  destruct s; simpl. destruct e3; simpl.
    
    Ltac save Hg :=
      repeat match goal with 
        |  H : _ |= _ -- _ |- _ =>
           pose proof (inv_1 Hg _ _ _ H);
           pose proof (inv_2 Hg _ _ _ H);
                    clear H
      end. 
    save Hg. simpl in *; subst. inversion H0; reflexivity. 
    save Hg. simpl in *; subst. inversion H0. reflexivity.    
    reflexivity. 
    reflexivity. 
  - simpl. clear H. 
    induction l; repeat DList.inversion;simpl; intuition. 
    + crush; eauto. 

Qed. 
Hint Resolve inv_bdd_wf.

Lemma  incr_inv G E (INV : inv G E) ptr E' e : 
  forall (H : incr eval_type E e = (ptr, E')), 
    inv (cons eval_type V B e (e, Some ptr) G) E'. 
Proof. 
  intros H; unfold incr in H. 
  destruct (BDD.mk_var (Ebdd E) (Enext E)) as [r bdd] eqn: Heq. 
  inject H.
  constructor. 
  intros. 
  - d. inversion X; injectT. inject H2. reflexivity. 
    apply INV. auto. 
  - intros x x' e'. inversion 1; injectT. clear X.
    unfold value. inject H0. simpl.
    eapply BDD.mk_var_pcorrect; eauto.  
    erewrite <- inv_next_2; eauto. 
    unfold value. simpl. 
    eapply BDD.pvalue_env_snoc. eapply inv_2 in X0; eauto. eapply BDD.mk_var_incr in Heq; eauto.

  - intros x x' e'. inversion 1; injectT. clear X. 
    inject H0. simpl. 
    eapply BDD.mk_var_path; eauto. 
    simpl. 
    eapply inv_path in X0;eauto. eapply BDD.mk_var_incr in Heq; eauto. 
  - simpl. eapply BDD.mk_var_incr in Heq; eauto. 
  - simpl. rewrite List.app_length. simpl. erewrite inv_next_2;eauto. rewrite plus_comm. reflexivity.
  - simpl. intros x y H. apply In_skip. apply INV. auto.  
Qed. 

Lemma lookup_in E ptr x: 
  lookup eval_type E ptr = Some x -> 
  Seq.In (ptr,x) (Eassoc E). 
Proof. 
  unfold lookup. induction (Eassoc E). simpl. discriminate. 
  simpl. destruct a.
  destruct (BDD.expr_eqb ptr e) eqn: Heq. 
  intros H; inject H.  
  apply BDD.expr_eqb_correct in Heq; subst.
  apply Seq.In_cons. 

  intros H. right. auto. 
Qed. 

Lemma add_bdd_correct G E E' (INV: inv G E) sv v ptr: 
  bvalue E sv v -> 
  add_bdd eval_type E sv = Some (ptr, E') -> 
  (value E' ptr v * inv G E' )%type. 
Proof. 
  destruct sv; simpl; intros H H'; simpl_do; inversion H; injectT.
   
  - split; eauto.  
  - refine (let (Hv, Hi) := BDD.ite_pcorrect (Ebdd E) (inv_bdd_wf INV  : BDD.wf (Ebdd E))
                                      _ _ _ c l r _ H0 _ H4 _ H6 _ H7 in _ ). 
    split; eauto. 
    Lemma inv_update_bdd G E bdd' (Hincr: BDD.incr (Ebdd E) bdd')
    : inv G E -> 
      inv G 
          {| Ebdd := bdd'; 
             Eassoc := Eassoc E; 
             Evalues := Evalues E; 
             Enext := Enext E|}. 
      Proof. 
        intros INV. constructor; try apply INV. 
        simpl. intros. unfold value. simpl. eapply BDD.pvalue_incr; eauto. apply (inv_2 INV) in X; apply X.  
        intros. simpl. eapply BDD.incr_path. eapply (inv_path INV) in X; apply X. 
        simpl. apply Hincr. apply INV. 
      Qed.         
      apply inv_update_bdd; auto.  
      
  - refine (let (Hv,Hi) := BDD.andb_pcorrect (Evalues E) (Ebdd E) (inv_bdd_wf INV) _ _ _ _ x0 H0 va H3 vb H5 in _).
    split; eauto using inv_update_bdd. 
  - refine (let (Hv,Hi) := BDD.orb_pcorrect (Evalues E) (Ebdd E) (inv_bdd_wf INV) _ _ _ _ x0 H0 va H3 vb H5 in _).
    split; auto using inv_update_bdd. 
  - refine (let (Hv,Hi) := BDD.xorb_pcorrect (Evalues E) (Ebdd E)  (inv_bdd_wf INV) _ _ _ _ x0 H0 va H3 vb H5 in _).
    split; auto using inv_update_bdd.     
  - refine (let (Hv,Hi) := BDD.negb_pcorrect (Evalues E) (Ebdd E) (inv_bdd_wf INV) _ _ _  x0 H0 va H2 in _).
    split; auto using inv_update_bdd. 
Qed. 

Lemma add_bdd_correct_2 G E E' (INV: inv G E) sv v ptr: 
  bvalue E sv v -> 
  add_bdd eval_type E sv = Some (ptr, E') -> 
  forall x vx, 
    value E x vx -> value E' x vx. 
Proof. 
  destruct sv; simpl; intros H H'; simpl_do; inversion H; injectT; clear H; auto. 
  - refine (let (Hv, Hi) := BDD.ite_pcorrect (Ebdd E) (inv_bdd_wf INV : BDD.wf (Ebdd E))
                                      _ _ _ c l r _ H0 _ H5 _ H7 _ H8 in _ ). 
    eapply BDD.pvalue_incr. eauto.  simpl. eauto. 
      
  - refine (let (Hv,Hi) := BDD.andb_pcorrect (Evalues E) (Ebdd E) (inv_bdd_wf INV) _ _ _ _ x0 H0 va H4 vb H6 in _).
    eauto using BDD.pvalue_incr. 
  - refine (let (Hv,Hi) := BDD.orb_pcorrect (Evalues E) (Ebdd E) (inv_bdd_wf INV) _ _ _ _ x0 H0 va H4 vb H6 in _).
    eauto using BDD.pvalue_incr. 
  - refine (let (Hv,Hi) := BDD.xorb_pcorrect (Evalues E) (Ebdd E) (inv_bdd_wf INV) _ _ _ _ x0 H0 va H4 vb H6 in _).
    eauto using BDD.pvalue_incr. 
  - refine (let (Hv,Hi) := BDD.negb_pcorrect (Evalues E) (Ebdd E) (inv_bdd_wf INV) _ _ _  x0 H0 va H2 in _).
    eauto using BDD.pvalue_incr. 
Qed. 

       
Lemma inv_cons_lookup_Some G E (INV : inv G E) E2 sv ptr old v:
  add_bdd eval_type E sv = Some (ptr, E2) -> 
  lookup eval_type E2 ptr = Some old -> 
  bvalue E sv v -> 
  inv (cons eval_type V B v (old, Some ptr) G) E2. 
Proof. 
  intros. 
  constructor. 
  -intros.  d. inversion X; injectT. inject H5. clear X. 
   simpl. 
   
   
   apply lookup_in in H0. 
   
   destruct (add_bdd_correct _ _ _ INV _ _ _ H1 H) as [Hv INV2].  
   apply (inv_assoc INV2) in H0. 
   apply (inv_2 INV2) in H0. 
   unfold value in *.           
   eapply BDD.pvalue_inj; eauto. 
   apply INV; auto. 
  - intros x x' e. 
    
    inversion 1; injectT.
    + clear X. inject H3. eapply add_bdd_correct in H; eauto.  intuition. 
    + eapply add_bdd_correct_2; eauto.  
      eapply inv_2 in X0; eauto. 
  - intros x x' e. inversion 1; injectT.  inject H3. 
    eapply add_bdd_correct in H; eauto.  destruct H as [Hv H'].
    eapply BDD.path_of_pvalue; eauto.
    
    eapply (inv_path).  2: eapply X0.
    eapply add_bdd_correct in H; eauto.  destruct H as [Hv H']. auto. 
  - exact (let (_,H) := @add_bdd_correct _ _ _ INV _ _ _ H1 H in 
           @inv_bdd_wf _ _ H). 
  -  eapply add_bdd_correct in H; eauto.  destruct H as [Hv H']. apply H'.  
  - intros.  eapply add_bdd_correct in H; eauto.  destruct H as [Hv H']. 
    apply In_skip. apply H'. eauto.  
Qed.

Lemma inv_cons_lookup_None G E (INV : inv G E) E2 sv ptr X:
  add_bdd eval_type E sv = Some (ptr, E2) -> 
  lookup eval_type E2 ptr = None -> 
  bvalue E sv X -> 
  inv (cons eval_type V B X (X, Some ptr) G) (add_env eval_type E2 X ptr). 
Proof. 
  intros. 
  constructor. 
  -intros.  d. inversion X0; injectT. inject H5. reflexivity. 
   eapply inv_1; eauto.     
  - intros x x' e. inversion 1; injectT. inject H3.  
    destruct (add_bdd_correct _ _ _ INV _ _ _ H1 H) as [Hv INV2].  
    unfold add_env. 
    unfold value. simpl. unfold value in Hv. apply Hv.
    unfold value. simpl. 
    eapply inv_2 in X1.
    apply X1.     destruct (add_bdd_correct _ _ _ INV _ _ _ H1 H) as [Hv INV2].  eauto. 
  - intros x x' e. inversion 1; injectT.  inject H3. 
    eapply add_bdd_correct in H; eauto.  destruct H as [Hv H'].
    eapply BDD.path_of_pvalue; eauto.

    simpl. 
    eapply (inv_path). 2: eapply X1.
    eapply add_bdd_correct in H; eauto.  simpl. destruct H as [Hv H']. auto. 
  - exact (let (_,H) := @add_bdd_correct _ _ _ INV _ _ _ H1 H in 
           @inv_bdd_wf _ _ H). 
  -  eapply add_bdd_correct in H; eauto.  destruct H as [Hv H']. apply H'.  
  - intros. 
    simpl in X0.
    apply Seq.In_app in X0. 
    eapply add_bdd_correct in H; eauto.  destruct H as [Hv H']. 
    destruct X0. 
    apply In_skip.    
    apply H'.  auto. 
    inversion i; subst. 
    apply In_ok. reflexivity. reflexivity. 
    inversion H2. 
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
             | HG : inv ?G ?e , H : In _ _ _ ?x ?y _ |- context [?x] =>
               rewrite (inv_1 HG _ _ _ H)
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
       pose proof (cp_expr_correct _ _ _ _ H _ _ _ He INV sv). rewrite Heq in H0. simpl in H0. 
       specialize (H0 eq_refl). 
       eapply inv_cons_lookup_Some; eauto.  
       pose proof (cp_expr_correct_2 _ st _ _ INV _ _ _ He _ _ Heq). 
       rewrite H. 
       pose proof (cp_expr_correct _ _ _ _ H _ _ _ He INV sv). simpl in H0.
       rewrite Heq in H0. simpl in H0. specialize (H0 eq_refl). 

       eapply inv_cons_lookup_None; eauto. 
       apply inv_cons_None; eauto using cp_expr_correct_2. 
    }
    {
      simpl. 
      destruct (incr eval_type E (eval_expr Phi st B binding)) as [ptr E'] eqn: Hincr.
      apply IH; clear IH. 
      eapply cp_expr_correct_2 in Heq; eauto.  
      rewrite Heq; clear Heq.  
      revert Hincr. 
      generalize (eval_expr Phi st B binding). 
      intros e H.
      eapply incr_inv; eauto. 
    }

Qed.   

Lemma Gamma_inv_empty : inv  (nil _ _ ) (empty eval_type). 
Proof. 
  econstructor. 
  - intros. inversion X. 
  - intros. inversion X. 
  - intros. inversion X. 
  - intros. apply BDD.wf_empty.  
  - simpl. reflexivity. 
  - simpl. intros.  inversion H. 
Qed. 

Theorem cp_correct Phi st t (b : Block Phi t) Delta : WF Phi t b -> 
  eval_block Phi st t (b _) Delta = eval_block Phi st t (cp_block Phi eval_type t (b _)) Delta. 
Proof. 
  intros.
  eapply cp_telescope_correct; eauto using Gamma_inv_empty.
Qed. 
  

Definition Compile Phi t (b : Block Phi t) : Block Phi t :=  
  fun V => cp_block Phi V t (b _). 

Theorem Compile_correct Phi t b (Hwf : WF Phi t b) st : 
  Next Phi st t (Compile Phi t b) =  Next Phi st t b. 
Proof. 
  unfold Next. intros. unfold Compile. symmetry. rewrite cp_correct; auto. 
Qed. 
