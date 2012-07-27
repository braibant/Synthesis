Require Common Core Flat.

(* Solutions for common sub expressions elimination environments:

- use a list of {t : type & x : expr t}, and use the fact that types
   are decidable to be sure lookups work fine

- use one list for each type 

- do not use lists (but loose some sharing)

*)
Import Common Core. 

Section t. 
  Variable Phi : state. 
  Variable st : eval_state Phi. 

  Inductive sval : type -> Type :=
  | SVar: forall t, nat -> sval t
  (* | SRead : forall t, Common.var Phi (Treg t) -> sval t *)
  | SConstant : forall t, constant t -> sval t
  | SMux : forall t, sval Tbool -> sval t -> sval t -> sval t
  | STuple : forall l, DList.T sval l ->  sval (Ttuple l)
  | SBuiltin : forall arg res (f : Core.builtin arg res), 
                 DList.T sval arg -> 
                 sval res. 

    
  Section induction. 
    (** Since the induction principle that is generated is not
      useful, we have to define our own.  *)
    
      Variable P : forall t : type, sval t -> Prop.  
      Hypothesis Hvar : forall (t : type) (v : nat), P t (SVar t v). 
      Hypothesis Hconstant : 
      forall (ty : type) (c : constant ty), P ty (SConstant ty c). 
      Hypothesis Hmux : forall (t : type) (e : sval B) (l r : sval t),
                          P B e -> P t l -> P t r ->  P t (SMux t e l r ).  
      Hypothesis Htuple : forall (l : list type) (exprs : DList.T sval l),
                            DList.Forall _ _ P l exprs -> 
                            P (Ttuple l) (STuple l exprs). 
      Hypothesis Hbuiltin : 
      forall (args : list type) (res : type) (f0 : builtin args res)
        (t : DList.T sval args), 
        DList.Forall _ _ P args t ->
        P res (SBuiltin args res f0 t). 

      Lemma sval_ind_alt (t : type) (sv : sval t) :  P t sv. 
      refine (let fix fold (t : type) (sv : sval t) :  P t sv  := 
                  match sv with
                    | SVar t x => Hvar t x
                    | SConstant t x => Hconstant t x
                    | SMux t x x0 x1 => Hmux t _ _ _ (fold _ x) (fold _ x0) (fold _ x1)
                    | STuple l x => Htuple l x _ 
                    | SBuiltin arg res f x => Hbuiltin arg res f _ _
                  end in fold t sv). 
      {
        induction x. simpl; apply I.
        split; [apply fold | apply IHx]; auto.      
      }
      { clear f. 
        induction x. simpl; apply I. 
        split; [apply fold | apply IHx]; auto. }
      Qed. 
  End induction. 


  Arguments STuple {l}%list _%dlist. 
  Arguments SBuiltin {arg res} f _%dlist. 

  Definition type_cast {P : type -> Type} {t} t' (x : P t) : option (P t'). 
  case_eq (type_eqb t t'). 
  intros. apply (type_eqb_correct t t') in H. subst. apply Some. auto. 
  intros. apply None. 
  Defined.

  Definition eval_sval t ( sv : sval t) (env : list ({t : type & eval_type t}) )  : option (eval_type t).
  refine (let fix eval_sval t (sv : sval t) : option (eval_type t) := 
              let fold :=
                  (fix fold l dl  : option (eval_type (Ttuple l)):=
                   match dl in DList.T _ l return option (eval_type (Ttuple l)) with 
                                                | [] => Some tt
                                                | t::q => 
                                                    do t <- eval_sval _ t;
                                                    do q <- fold _ q;
                                                    Some (t,q)
                   end%dlist)
              in
                match sv with              
                  | SVar t n => 
                      do tx <- List.nth_error (env) n;
                      match tx with 
                          existT t' x => 
                            type_cast t x
                      end 
                            
                  (* | SRead t v => Some (Common.DList.get v st) *)
                  | SConstant t x => Some x
                  | SMux t c l r  => 
                      do c <- eval_sval _ c;
                      do l <- eval_sval _ l;
                      do r <- eval_sval _ r;
                      Some (if c then l else r)
                | STuple l x => 
                    fold _ x
                | SBuiltin arg res f x => 
                    do x <- fold _ x;
                    Some (builtin_denotation _ _ f x)
              end in eval_sval t sv).
  Defined. 


  Definition fstT (t : type) := 
    option (sval (match t with | Ttuple (a :: _) => a| _ => t end)).
  
  Definition sndT (t : type) := 
    option (sval (match t with | Ttuple (_ :: q) => Ttuple q | _ => t end)).
  
  Definition nthT (t' : type) t : Type :=   
    match t' with | Ttuple l => Common.var l t| _ => (unit : Type)end ->
    option (sval (match t' with | Ttuple l => t | _ => t' end)). 
  
  Variable Var : Core.type -> Type.
  Notation V := (fun t => Var t * sval t)%type. 
  Import Flat. 
  Notation "!!" := (None). 

  
  Definition cse_expr t (e : expr Phi V t) : expr Phi Var t * option (sval t). 
  refine (
      match e  with
        (* | Eread t v => (Eread _ _ t v, Some (SRead t v))  *)
        | Eread t v => (Eread _ _ t v, !!)
        | Eread_rf n t v adr =>   (Eread_rf _ _ _  t v (fst adr), !! )
        | Ebuiltin args res f x => let v := DList.map (fun x dx => fst dx) x in 
                                    let sv  := DList.map (fun x dx => snd dx) x in                                     (Ebuiltin _ _ args res f v ,  Some (SBuiltin f sv) ) 
        | Econstant ty c =>  (Econstant _ _ _ c, Some (SConstant _ c)) 
        | Emux t c l r =>   (Emux _ _ _ (fst c) (fst l) (fst r), !!) 
        | Efst l t x => (Efst _ _ _ _ (fst x), 
                        match snd x in sval t' return fstT t' with
                          | @STuple (_ :: _) dl => Some  (DList.hd  dl)
                          | _ => !!
                        end)
        | Esnd l t x => (Esnd _ _ _ _ (fst x), 
                        match snd x in sval t' return sndT t' with
                          | @STuple (t::q) dl => Some  (@STuple q (DList.tl  dl))
                          | _ => !!
                        end)
        | Enth l t m x => (Enth _ _ _ _ m (fst x), 
                          match snd x in sval t' return nthT  t' t 
                          with
                            | @STuple l dl => fun m => Some (DList.get  m dl)
                            | _ => fun _ => !!
                          end m) 
        | Etuple l exprs => let x := DList.map (fun x dx => fst dx) exprs in 
                            let y := DList.map (fun x dx => snd dx) exprs in 
                             (Etuple _  _ l x, Some (STuple  y))
      end). 

  Defined. 

  Definition sval_eqb : forall a b, sval a -> sval b -> bool.  
  refine (let fix eqb {a b} (va : sval a) (vb : sval b) : bool :=
              let fix pointwise  la lb (dla : DList.T sval la) (dlb : DList.T sval lb) : bool :=
                  match dla, dlb with 
                    | [] , [] => true
                    | t::q , t' :: q' => (eqb t t' && pointwise _ _ q q')%bool
                    | _, _ => false
                  end%dlist in 

              match va, vb with
                (* | SRead ta va, SRead tb vb => var_eqb va vb  *)
                | SVar ta na, SVar tb nb  => type_eqb ta tb && NPeano.Nat.eqb na nb
                | SConstant ta ca, SConstant tb cb =>
                    _
                | SMux ta ca la ra, SMux tb cb lb rb => 
                    type_eqb ta tb && eqb ca cb && eqb la lb && eqb ra rb
                | STuple la dla, STuple lb dlb => pointwise la lb dla dlb
                | SBuiltin _ _ fa dla , SBuiltin _ _ fb dlb => 
                    builtin_eqb fa fb && pointwise _ _ dla dlb
                | _, _ => false
              end%bool in @eqb). 
  (* The constant case, requires a cast *)
  case_eq (type_eqb ta tb). intros. apply type_eqb_correct in H. subst. 
  apply (type_eq tb ca cb). 
  exact (fun _ => false). 
  Defined. 
  
  Definition Env := list ({t : type & (sval t * Var t)%type}). 

  Definition empty : Env := ([])%list. 

  Fixpoint lookup (t : type) (sv: sval t) (E : Env) : option (Var t) :=
    match E with 
      | [] => None
      | existT  t' (sv',x)::q => 
          (if type_eqb t' t as b 
              return type_eqb t' t = b -> option (Var t)
           then
             (fun H : type_eqb t' t = true  => 
                let H := type_eqb_correct t' t H in 
                  if sval_eqb _ _ sv sv' 
                  then Some (eq_rect t' Var x t H)
                  else lookup _ sv q                                 
             )
              else 
            fun _ => lookup t sv q) eq_refl
    end%list. 

  Definition add (t : type) (sv : sval t) (v : Var t) (env : Env) : Env :=
    ( env ++ [existT _ t (sv,v)])%list . 

  (* Unfortunately, multiple reads from the same state elements cannot be shared *)
  Definition cse_telescope {A} (E: Env) (T : telescope Phi V A) : telescope Phi Var A. 
  refine (let fix cse F T :=
              match T with
                | & x => & x
                | telescope_bind arg b cont => _
              end in cse E T). 
  refine (let (e,svo) := cse_expr arg b in _). 
  refine (match svo with 
              | None => k :- e; 
                  let sv := (SVar arg (List.length F)) in
                    let F := add arg  sv k F in
                      cse F (cont (k,sv))
              | Some sv =>                   
                  match lookup arg sv F with 
                    | None =>     
                        k :-  e; 
                        let F := add arg  sv k F in
                          cse F (cont (k,sv))
                    | Some old => cse F (cont (old, sv))
                  end
          end).                                     
  Defined. 


  Definition cse_effects (eff: effects Phi V) : effects Phi Var. 
  refine( DList.map  _  eff). 
  intros a x. 
  refine (match x with 
            | None => None
            | Some x => match x with
                         | effect_reg_write t x x0 => 
                             Some (effect_reg_write _ t (fst x) (fst x0))
                         | effect_regfile_write n t x x0 x1 => 
                             Some (effect_regfile_write _ n t (fst x) (fst x0) (fst x1)  )
                       end
          end). 
  Defined. 
  
  Definition cse_block  t (b : block Phi V t) : block Phi Var t :=    
    k :-- cse_telescope empty b;
    match k with (v,g,e) =>
                   & (fst v, fst g, cse_effects  e)
    end. 
End t. 

Import Flat. 

Notation V := (fun t => (eval_type t * sval t))%type.  

Require Import Eqdep. 


Ltac t :=  subst; repeat match goal with 
                       H : existT _ _ _ = existT _ _ _ |- _ => 
                         apply Eqdep.EqdepTheory.inj_pair2 in H
                   |   H : context [eq_rect ?t _ ?x ?t ?eq_refl] |- _ => 
                         rewrite <- eq_rect_eq in H
                   |   H : context [eq_rect ?t _ ?x ?t ?H'] |- _ => 
                         rewrite (UIP_refl _ _ H') in H;
                         rewrite <- eq_rect_eq in H
                   |   H : existT _ ?t1 ?x1 = existT _ ?t2 ?x2 |- _ => 
                         let H' := fresh "H'" in 
                           apply eq_sigT_sig_eq in H; destruct H as [H H']; subst
                         end; subst.


Ltac d :=
  match goal with 
   H : context [do _ <- ?x; _] |- _ =>
     let A := fresh in 
     case_eq x; [intros ?X A | intros A]; rewrite A in H; simpl in H
  | |- context [do _ <- ?x; _] =>
     case_eq x; intros; simpl
  end.
Ltac f := 
  match goal with 
      |- context [fst ( _ , _ )] => simpl
    | |- context [fst ?x] => destruct x; simpl
    | |- context [Tuple.fst ( _ , _ )] => simpl
    | |- context [Tuple.fst ?x] => destruct x; simpl
    | |- context [snd ( _ , _ )] => simpl
    | |- context [snd ?x] => destruct x; simpl
    | |- context [Tuple.snd ( _ , _ )] => simpl
    | |- context [Tuple.snd ?x] => destruct x; simpl
  end;
  try (congruence || discriminate). 
Notation "G |= x -- y" := (In _ _ _ x y G) (no associativity, at level 71). 

Notation R := (fun G t x y => In _ _ t x y G).  

Definition lift (env : Env eval_type) : list ({t : type & eval_type t}). 
refine (List.map _ env). 
refine (fun x => match x with  existT t (sv,v) => existT _ t v end). 
Defined. 

Record Gamma_inv (G : Gamma eval_type V) (E : Env eval_type) :=
  {
    Gamma_inv_1 : forall t (x : eval_type t) y, G |= x -- y -> x = fst y;
    Gamma_inv_2 : forall t x y, G |= x -- y -> eval_sval t (snd y) (lift E) = Some x;
    Gamma_inv_3 : forall t x sv, List.In (existT _ t (sv , x))  E -> G |= x -- (x,sv)
  }. 
 
Hint Resolve Gamma_inv_1 Gamma_inv_2 Gamma_inv_3. 

Ltac use :=
  match goal with 
    | Hgamma : Gamma_inv ?G _,  H : ?G |= ?x -- ?y |- context [?x] =>
        rewrite (Gamma_inv_1 _ _  Hgamma _ _ _ H) 
  end. 


Section test. 
  Import Equality. 
  Lemma cse_expr_correct Phi st : forall t e1 r1, 
  eval_expr Phi st t e1 = r1 ->
  forall G (env : Env eval_type) e2,
    expr_equiv _ _ Phi (R G) t e1 e2 ->     
    (forall t (x : eval_type t) y, G |= x -- y -> x = fst y)  ->
    (forall t (x : eval_type t) y, G |= x -- y -> eval_sval t (snd y) ( lift env) = Some x)
    -> match snd (cse_expr Phi _ t  e2) with
        | Some sv => eval_sval  t sv ( lift env) = Some r1
        | None => True
      end.
Proof. 
  destruct 1; inversion 1; t;  try solve [simpl; auto].  
  - intros. 
    clear H. 
    simpl. 
    d. repeat f_equal. 
    revert H. clear f. 
    induction args. 
    simpl; repeat DList.inversion.  simpl. congruence. 
    simpl. repeat DList.inversion. simpl in *. repeat d. repeat f_equal.

    apply DList.inversion_pointwise in H3. destruct H3.   
    pose proof (H1 _ _ _ H5). destruct o. 
    f_equal. congruence. 
    apply (IHargs x2) in H4. 
    congruence.  auto.

    discriminate. 
    discriminate. 
    discriminate. 
    simpl. 
    
    apply False_rect. 
    clear f. 
    
    induction args. 
    repeat DList.inversion. simpl in *. discriminate.
    repeat DList.inversion. simpl in *. repeat d; try discriminate.
    apply DList.inversion_pointwise in H3. eapply IHargs.
    destruct H3. apply H3. apply H4.  
    apply DList.inversion_pointwise in H3. 
    destruct H3. apply H1 in H4. congruence. 

  - intros.  simpl. 
    destruct dl2 as [hd tl].  simpl. dependent destruction tl; try tauto.
    specialize (H0 _ _ _ H3). 
    specialize (H1 _ _ _ H3). 
    DList.inversion; subst. simpl in *; repeat d; f. 
  - t .  intros. 
    specialize (H1 _ _ _ H2).
    specialize (H3 _ _ _ H2).
    simpl.     destruct dl2 as [hd tl].  simpl. dependent destruction tl; try tauto.
    subst. simpl in *.   DList.inversion. subst. simpl. 
    repeat d; f. 
  - intros. simpl.  
    destruct dl2 as [hd tl]. simpl.  dependent destruction tl; try tauto.
    simpl. 
    clear H.
    specialize (H1 _ _ _ H3). clear H3. 
    induction v. 
    + simpl. simpl in H1. DList.inversion. subst.      
      
      repeat d; simpl; f.  
    + simpl. 
      erewrite IHv. reflexivity. 
      simpl. 
      DList.inversion. subst. simpl. simpl in H1. 
      repeat d; simpl; f. 
  - intros.  simpl. 
    t.   clear H H0 H4. 
    induction l. 

    + simpl; repeat DList.inversion. 
      simpl in *. 
      reflexivity. 
    + repeat DList.inversion. simpl in *. 
    destruct (DList.inversion_pointwise _ _ _ _ _ _ _ H2). clear H2. 
    
    repeat d; subst.
    * erewrite IHl in H4. clear IHl.  2: apply H. solve [firstorder congruence]. 
    * erewrite IHl in H4. clear IHl.  2: apply H. congruence. 
    * clear IHl.    firstorder congruence. 
    
    Grab Existential Variables. 
    simpl in *. destruct dl1.  auto. 
Qed. 
End test. 


 
Lemma lem1 Phi st env G  t e1 e2 e'  sv : 
  expr_equiv eval_type V Phi (Flat.R eval_type V G) t e1 e2 ->
  Gamma_inv G env ->
  cse_expr Phi eval_type t e2 = (e', Some sv) ->
  eval_sval t sv (lift env) = Some (eval_expr Phi st t e1). 
Proof. 
  intros H H1 H2.  
  pose (H' := cse_expr_correct _ st _ _ (eval_expr Phi st t e1) (refl_equal)). 
  specialize (H' G env e2 H). 
  specialize (H' (Gamma_inv_1 _ _ H1) (Gamma_inv_2 _ _ H1)).
  rewrite H2 in H'.
  apply H'. 
Qed.

Lemma type_eqb_refl : forall t, type_eqb t t = true. 
induction t using type_ind; simpl;  firstorder. 
apply NPeano.Nat.eqb_eq. reflexivity. 
apply NPeano.Nat.eqb_eq. reflexivity. 
Qed. 
 
Section protect00. 
Import Equality. 
Lemma sval_eqb_correct t (sv sv' : sval t) : sval_eqb t t sv sv' = true -> sv = sv'. 
Proof. 
  revert sv'. 
  induction sv using sval_ind_alt; dependent destruction sv'; simpl;
  intros;
  repeat 
    match goal with 
        H: (?x && ?y)%bool = true |- _ => rewrite Bool.andb_true_iff in H; destruct H
      | H : type_eqb _ _ = true |- _ => apply type_eqb_correct in H
      | H : NPeano.Nat.eqb _ _ = true |- _ => apply NPeano.Nat.eqb_eq in H
    end; subst; try discriminate; auto.
  - revert H. 
  generalize (type_eqb_refl t). 
  generalize (type_eqb_correct t t). 
  destruct (type_eqb t t); try discriminate.  
  intros. unfold eq_rect_r in H0. rewrite (UIP_refl _ _ (e eq_refl)) in H0.
  rewrite (UIP_refl _ _ (eq_sym eq_refl)) in H0. 
  rewrite <- eq_rect_eq in H0. 
  clear - H0. admit. 
  - repeat match goal with 
      | H : forall t, _ -> _ , H' : _ |- _ => apply H in H'; clear H; rewrite H'
  end. reflexivity.
  - induction l; repeat DList.inversion. reflexivity.   
    simpl in *. rewrite Bool.andb_true_iff in H0. destruct H0.
    repeat f_equal. 
    destruct H. auto. 
    destruct H. specialize (IHl _ H2 _ H1). clear - IHl. injection IHl; intros; t; auto. 
Admitted. 

End protect00. 

Lemma lookup_1 env t (sv : sval t) e :
  lookup eval_type t sv (env) = Some e ->
  List.In (existT _ t (sv,e)) (env). 
Proof.
  intros. 
  induction env. discriminate.
  destruct a as [t' [sv' x']]. simpl in H.
  revert H. generalize (type_eqb_correct t' t). destruct (type_eqb t' t).  simpl. intros.
  pose proof (e0 eq_refl). subst. 

  case_eq (sval_eqb t t sv sv'); intros.    
  left. t. rewrite H0 in H. 
  repeat f_equal; try congruence || symmetry; auto using sval_eqb_correct. 
  right.  apply IHenv. rewrite H0 in H.  auto. 
  intros. 
  simpl. right. auto. 
Qed. 

Lemma lem2  G env t e1 e2 sv : 
  List.In (existT _ t (sv,e2)) (env) ->
  Gamma_inv G env ->
  eval_sval t sv (lift env) = Some e1 ->
  G |= e1 -- (e2, sv). 
Proof. 
  intros. apply (Gamma_inv_3 _ _ H0) in H. 
  pose proof (Gamma_inv_2 _ _ H0 _ _ _ H). 
  simpl in H2. 
  
  assert ( e1 = e2). congruence.
  subst; auto. 
Qed. 

Lemma lemma_2 Phi st env G  t e1 e2 e3 e'  sv : 
  expr_equiv eval_type V Phi (Flat.R eval_type V G) t e1 e2 ->
  Gamma_inv G env ->
  cse_expr Phi eval_type t e2 = (e', Some sv) ->
  lookup eval_type t sv (env) = Some e3 ->
  eval_expr Phi st t e1 = e3. 
Proof. 
  intros. 
  assert (eval_sval t sv (lift env) = Some (eval_expr Phi st t e1)). eauto using lem1.
  
  apply lookup_1 in H2.   
  apply (Gamma_inv_3 _ _ H0) in H2. 
  apply (Gamma_inv_2 _ _ H0) in H2. 
  simpl in H2. congruence. 
Qed. 

Lemma Gamma_inv_cons G env t e sv : 
  Gamma_inv G env ->
  eval_sval t sv (lift env)  = Some e ->
  Gamma_inv (cons eval_type V t e (e,sv) G) env. 
Proof. 
  intros. constructor. 
  - intros. inversion H1; t. reflexivity. eauto. 
  - intros. inversion H1; t. simpl. eauto.  eauto. 
  - intros. apply In_skip. eauto. 
Qed. 

Ltac clean := repeat match goal with H : ?x = ?x |- _ => clear H end. 

Section protect. 
Lemma cse_effects_correct Phi st Delta G e  (Hg : Gamma_inv G e):
  forall e1 e2 
  (H : effects_equiv eval_type V Phi (Flat.R eval_type V G) e1 e2), 
   eval_effects Phi st e1 Delta =
   eval_effects Phi st (cse_effects Phi eval_type e2) Delta. 
Proof. 
  intros e1 e2 H. induction H; subst; repeat t; subst. 
  - simpl; reflexivity. 
  - intros. 
    clean. 
    simpl. 
    Import Equality.     
    repeat match goal with 
      |- context [match ?x with _ => _ end] => first [destruct x | dependent destruction x]
    end; intros;
    unfold eval_state in *; repeat DList.inversion; subst; simpl in *;
    intros; inversion H; t; unfold Flat.R in *; simpl; repeat auto;
    repeat match goal with 
      |- (_ :: _ = _ :: _)%list => f_equal
    | |- (_ :: _ = _ :: _)%dlist => f_equal
    | |- _ => auto
    end. 
    destruct x; [reflexivity | repeat use; reflexivity]. 
    destruct x; [reflexivity | repeat  use; reflexivity]. 
Qed. 
End protect. 

Lemma type_cast_eq t (e : eval_type t) : type_cast t e = Some e. 
Proof. 
  unfold type_cast.
  generalize (type_eqb_correct t t). intros. 
  assert (H := type_eqb_refl). 
  generalize (H t). 
  destruct (type_eqb t t). 
  
  rewrite (UIP_refl _ _ (e0 eq_refl)).  
  simpl. reflexivity. 
  discriminate. 
Qed. 

Lemma nth_error_app {A} l :
  forall l' n (x : A), List.nth_error l n = Some x ->
                  List.nth_error (l ++ l') n = Some x. 
Proof. 
  induction l. simpl. destruct n; discriminate. 
  simpl. intros. destruct n. simpl in *. auto. 
  
  simpl. auto. 
Qed.

Lemma eval_sval_monotone l l' t x : 
  forall sv,  
    eval_sval t sv l = Some x  ->
    eval_sval t sv (l ++ l') = Some x. 
Proof. 
  induction sv using sval_ind_alt. simpl. 

  d. simpl in H0.
  rewrite (nth_error_app _ _ _ _ H). simpl. auto. 
  simpl in *. discriminate. 
  simpl. auto. 
  simpl in *. 
  intros.  invert_do H. 
  
  repeat match goal with 
      | H : forall t, _ -> _ , H' : _ |- _ => apply H in H'; clear H; rewrite H'
  end. reflexivity.
  
  induction exprs. simpl. auto.
  intros H'.
  simpl in H. destruct H as [Hhd Htl]. 
  simpl. simpl in H'.  invert_do H'. apply Hhd in EQ. rewrite EQ. clear EQ. simpl. 
  apply IHexprs in EQ1; auto. simpl in EQ1. rewrite EQ1. simpl. reflexivity. 
  
  simpl.  
  assert (forall x, 
      let dl := (fix fold (l0 : list type) (dl : DList.T (fun H0 : type => sval H0) l0)
              {struct dl} : option (Tuple.of_list eval_type l0) :=
       match
         dl in (DList.T _ l1) return (option (Tuple.of_list eval_type l1))
       with
       | DList.nil => Some tt
       | DList.cons t0 q0 t1 q =>
           do t2 <- eval_sval t0 t1 l; do q1 <- fold q0 q; Some (t2, q1)
       end) args t in 
        dl = Some x -> 
      (fix fold (l0 : list type) (dl : DList.T (fun H0 : type => sval H0) l0)
           {struct dl} : option (Tuple.of_list eval_type l0) :=
       match
         dl in (DList.T _ l1) return (option (Tuple.of_list eval_type l1))
       with
         | DList.nil => Some tt
         | DList.cons t0 q0 t1 q =>
             do t2 <- eval_sval t0 t1 (l ++ l');
             do q1 <- fold q0 q; Some (t2, q1)
       end) args t  = Some x
         ). 
  clear - H. induction t.
  simpl. auto. 
  
  simpl. intros. 
  
  simpl in H. destruct H as [Hhd Htl]. specialize (IHt Htl).
  case_eq (eval_sval t p l). 
  intros. rewrite H in H0.  apply Hhd in H. rewrite H. simpl. simpl in H0. 
  invert_do H0. apply IHt in EQ.  rewrite EQ. simpl. reflexivity. 
  intros.
  rewrite H in H0. simpl in H0. discriminate. 
  intros H'. invert_do H'. apply H0 in EQ. rewrite EQ. simpl. 
  reflexivity. 
Qed. 

Lemma list_in_snoc {A} l (x y : A) : List.In x (l++[y]) -> List.In x l \/  x = y. 
Proof. 
  revert x y. induction l. simpl; intuition.
  simpl. intros x y [H | H]; auto. 
  apply IHl in H. intuition.
Qed. 
  

Lemma nth_error_map {A B} {f : A -> B} l t  :
  List.nth_error (List.map f (l ++ [t])) (List.length l) = Some (f t). 
Proof. 
  induction l. reflexivity. 
  simpl. auto. 
Qed. 

Section protect0. 
Import Equality. 
Lemma cse_expr_correct_2 Phi st G env (Hg : Gamma_inv G env) t:
  forall e1 e2, expr_equiv eval_type V Phi (Flat.R eval_type V G) t e1 e2 ->
           forall svo e, cse_expr Phi eval_type t e2 = (e,svo) ->
                           eval_expr Phi st t e1 = eval_expr Phi st t e. 
Proof.
  intros e1. destruct e1; intros e2 H; inversion H; t; simpl; intros; unfold Flat.R in *. 
  - injection H0; intros; subst. clean. reflexivity. 
  - injection H0; intros; subst. clean. use. reflexivity. 
  - injection H0; intros; subst. clean. simpl. f_equal.
    clear H b. induction args. 
    + repeat DList.inversion.  simpl. reflexivity. 
    +   repeat DList.inversion. simpl. apply DList.inversion_pointwise in H2. destruct H2.  f_equal. eauto.  apply IHargs. auto. 
  -  injection H0; intros; subst. clean. reflexivity. 
  -  injection H0; intros; subst. clean. simpl. repeat use; reflexivity. 
  - destruct dl2. simpl in H0. 
    dependent destruction s;  injection H0; intros; subst; clean;
    simpl; use; reflexivity. 
  - destruct dl2. simpl in H0. 
    dependent destruction s;  injection H0; intros; subst; clean;
    simpl; use; reflexivity.        
  - destruct dl2. simpl in H0. 
    dependent destruction s;  injection H0; intros; subst; clean;
    simpl; use; reflexivity.      
  - injection H0; intros; subst; clean. simpl. 
    clear H. 
     induction l. 
    + repeat DList.inversion.  simpl. reflexivity. 
    +   repeat DList.inversion. simpl. apply DList.inversion_pointwise in H3. destruct H3.  f_equal. eauto.  apply IHl. auto. 
Qed. 
End protect0. 

Lemma Gamma_inv_cons_var G env (Hg : Gamma_inv G env) t (e : eval_type t): 
      Gamma_inv (cons eval_type V t e (e, SVar t (Datatypes.length env)) G)
                (add eval_type t (SVar t (Datatypes.length env)) e env). 
Proof.
  intros. 
  constructor; intros. 
  - inversion H; t. reflexivity.  use; reflexivity.  
  - inversion H; t. simpl. unfold lift. unfold add. simpl. 
    rewrite nth_error_map. simpl.
    
    apply type_cast_eq.
    apply (Gamma_inv_2 _ _ Hg) in H1.
    clear - H1. 
    unfold lift, add in *. 

    destruct y as [ y sv]. 
    rewrite List.map_app. 
    revert H1. 
    match goal with |- context [List.map ?f _] => set (F := f) end. 
    replace (List.length env) with (List.length (List.map F env)) by apply List.map_length.
    generalize (List.map F env).  intros. simpl. 
    clear F. simpl in H1.  
    apply eval_sval_monotone ; auto.    
    
    
  - unfold add in H.  apply list_in_snoc in H. 
    destruct H. apply In_skip. eauto. 
    t. apply In_ok. congruence. congruence. 
Qed.         
      
Lemma Gamma_inv_cons_other G env (Hg : Gamma_inv G env) t (e : eval_type t) sv: 
  eval_sval t sv (lift env) = Some e ->
  Gamma_inv (cons eval_type V t e (e, sv) G)
            (add eval_type t sv e env). 
Proof. 
  constructor. 
  - intros. inversion H0; subst; t; subst. reflexivity.   eauto. 
  - intros. inversion H0; subst; t; subst. 
    simpl. unfold lift, add. rewrite List.map_app. apply eval_sval_monotone. apply H.
    simpl. unfold lift, add. rewrite List.map_app. apply eval_sval_monotone. eapply Gamma_inv_2; eauto. 
  - intros.
  unfold add in H0; apply list_in_snoc in H0. 
  destruct H0. apply In_skip. eauto. 
  t. apply In_ok. congruence. 
  congruence. 
Qed. 


Theorem cse_correct Phi st t  Delta: 
     forall (b : block Phi eval_type t)
     (b' : block Phi V t)
     (G : Gamma eval_type V),
       block_equiv eval_type V Phi t G b b' ->
       forall e,
       Gamma_inv G e
     ->
   eval_telescope Phi st
     (fun x : eval_type t * bool * effects Phi eval_type =>
      let (y, e0) := x in
      let (p, g) := y in check g; Some (p, eval_effects Phi st e0 Delta)) b =
   eval_telescope Phi st
     (fun x : eval_type t * bool * effects Phi eval_type =>
      let (y, e0) := x in
      let (p, g) := y in check g; Some (p, eval_effects Phi st e0 Delta))
     (k :-- cse_telescope Phi eval_type e b';
      (let (p, e0) := k in
       let (v, g) := p in & (fst v, fst g, cse_effects Phi eval_type e0))). 
Proof. 
  induction 1.
  
  * simpl; intros; repeat use.
  simpl eval_type;
  match goal with |- context [check ?x; _] => destruct x; [|reflexivity]  end. 
  f_equal.   f_equal. 
  eapply cse_effects_correct; eauto. 
  
  * intros; simpl eval_telescope. clear H0. 
    case_eq (cse_expr Phi eval_type a e2). 
    destruct o. 
    case_eq (lookup eval_type a s (e)). intros. 
    simpl. 
    apply H1.

    { now_show ( Gamma_inv (cons eval_type V a (eval_expr Phi st a e1) (e3, s) G) e). 
      assert (eval_expr Phi st a e1 = e3). 
      pose proof (lem1 Phi st e G a _ _ _ s H H2 H3).
       
      eauto using lemma_2. 
      rewrite H4. 
      apply Gamma_inv_cons. auto. subst; eauto using lem1. 
    }
    
    intros. simpl. 
    apply H1. 
    assert (eval_expr Phi st a e0 = eval_expr Phi st a e1). 
    pose proof (H3). eapply lem1 in H4; eauto. 
    symmetry; eapply cse_expr_correct_2; eauto. 
    rewrite H4. 
    
    
    {
      clear H1. clear H4.
      assert (eval_sval a s (lift e) = Some (eval_expr Phi st a e1)). eauto using lem1. 
      
      apply Gamma_inv_cons_other; auto. 
    }
    
    intros. 
    apply H1.
    { clear H1. 
    assert (eval_expr Phi st a e1 = eval_expr Phi st a e0). 
    eapply cse_expr_correct_2; eauto. 
    rewrite H1 in *. generalize (eval_expr Phi st a e0). 
    clear  H1.   clear -H2.
    apply Gamma_inv_cons_var; auto. }


    Grab Existential Variables. 
    apply st. 
Qed. 
Print Assumptions cse_correct.
