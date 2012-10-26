Require Import Common DList Core Eqdep RTL. 


(** This file implements one pass of common sub-expression elimination. *)

Definition type_cast {P : type -> Type} {t} t' (x : P t) : option (P t') :=
  (if type_eqb t t' as b return (type_eqb t t' = b -> option (P t'))
   then
     fun H : type_eqb t t' = true =>
       (fun Heq : t = t' =>
          match Heq in (_ = t) return option (P t) with
            | eq_refl => Some x
          end) (type_eqb_correct t t' H)
   else fun _ => None) eq_refl. 

Lemma type_cast_inversion t t' (x:eval_type t') (y: eval_type t) : type_cast t x = Some y -> 
                                                                   t = t'. 
Proof. 
  unfold type_cast.
  
  generalize (type_eqb_correct t' t). simpl. pattern (type_eqb t' t). 
  destruct (type_eqb t' t); try discriminate. 
  intros e.
  pose proof (e eq_refl). subst. reflexivity. 
Qed. 

(* (** The dependent type swiss-knife. *) *)
(* Ltac t :=  subst; repeat match goal with  *)
(*                        H : existT _ _ _ = existT _ _ _ |- _ =>  *)
(*                          apply Eqdep.EqdepTheory.inj_pair2 in H *)
(*                    |   H : context [eq_rect ?t _ ?x ?t ?eq_refl] |- _ =>  *)
(*                          rewrite <- eq_rect_eq in H *)
(*                    |   H : context [eq_rect ?t _ ?x ?t ?H'] |- _ =>  *)
(*                          rewrite (UIP_refl _ _ H') in H; *)
(*                          rewrite <- eq_rect_eq in H *)
(*                    |   H : existT _ ?t1 ?x1 = existT _ ?t2 ?x2 |- _ => *)
(*                        let H' := fresh "H'" in *)
(*                          rewrite eq_sigT_iff_eq_dep in H; subst *)
(*                          end; subst. *)

Section s. 
  Variable Phi : state. 
  Variable st : eval_state Phi. 
  
  Section t. 
  (** The data-type of symbolic values: that is, values that are going
  to be compared and elimated in case of redundancy. *)

  Inductive sval : type -> Type :=
  | SVar: forall t, nat -> sval t
  | SRead : forall t, Common.var Phi (Treg t) -> sval t
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
      Hypothesis Hread : forall t v, P t (SRead t v).
      Hypothesis Hvar : forall (t : type) (v : nat), P t (SVar t v). 
      Hypothesis Hconstant : 
      forall (ty : type) (c : constant ty), P ty (SConstant ty c). 
      Hypothesis Hmux : forall (t : type) (e : sval B) (l r : sval t),
                          P B e -> P t l -> P t r ->  P t (SMux t e l r ).  
      Hypothesis Htuple : forall (l : list type) (exprs : DList.T sval l),
                            DList.Forall P exprs -> 
                            P (Ttuple l) (STuple l exprs). 
      Hypothesis Hbuiltin : 
      forall (args : list type) (res : type) (f0 : builtin args res)
        (t : DList.T sval args), 
        DList.Forall P t ->
        P res (SBuiltin args res f0 t).     

      Lemma sval_ind_alt (t : type) (sv : sval t) :  P t sv. 
      refine (let fix fold (t : type) (sv : sval t) :  P t sv  := 
                  match sv with
                    | SRead t v =>  Hread t v
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


  
  Section eval. 
    Variable env: list ({t : type & eval_type t}). 
    (** [eval_sval env sv] computes the denotation of [sv] in the environment [env] *)
    Fixpoint eval_sval {t} ( sv : sval t)   : option (eval_type t) :=
      let fold :=
          (fix fold l dl  : option (eval_type (Ttuple l)):=
           match dl in DList.T _ l return option (eval_type (Ttuple l)) with 
                                        | [ :: ] => Some tt
                                        | t::q => 
                                            do t <- eval_sval t;
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
          | SRead t v => Some (DList.get v st)
          | SConstant t x => Some x
          | SMux t c l r  => 
              do c <- eval_sval  c;
              do l <- eval_sval  l;
              do r <- eval_sval  r;
              Some (if c then l else r)
          | STuple l x =>  fold _ x
          | SBuiltin arg res f x => 
              do x <- fold _ x;
              Some (builtin_denotation _ _ f x)
        end.
  End eval. 


  Definition fstT (t : type) := 
    option (sval (match t with | Ttuple (a :: _) => a| _ => t end)).
  
  Definition sndT (t : type) := 
    option (sval (match t with | Ttuple (_ :: q) => Ttuple q | _ => t end)).
  
  Definition nthT (t' : type) t : Type :=   
    match t' with | Ttuple l => Common.var l t| _ => (unit : Type)end ->
    option (sval (match t' with | Ttuple l => t | _ => t' end)). 
  
  Variable Var : Core.type -> Type.
  
  Notation V := (fun t => Var t * sval t)%type. 
  
  Notation "!!" := (None). 

  Fixpoint sval_eqb {a b} (va: sval a) (vb : sval b) : bool :=
    let fix pointwise  {la lb} (dla : DList.T sval la) (dlb : DList.T sval lb) : bool :=
        match dla, dlb with 
          | [ :: ] , [ :: ] => true
          | t::q , t' :: q' => (sval_eqb t t' && pointwise q q')%bool
          | _, _ => false
        end%dlist in 
      
      match va, vb with
        | SRead ta va, SRead tb vb => var_eqb va vb
        | SVar ta na, SVar tb nb  => type_eqb ta tb && NPeano.Nat.eqb na nb
        | SConstant ta ca, SConstant tb cb =>
            match type_cast tb ca with | Some ca =>  type_eq tb ca cb | None => false end
        | SMux ta ca la ra, SMux tb cb lb rb => 
            type_eqb ta tb && (sval_eqb ca cb && sval_eqb la lb && sval_eqb ra rb)
        | STuple la dla, STuple lb dlb => pointwise dla dlb
        | SBuiltin arga _ fa dla , SBuiltin argb _ fb dlb => 
            type_list_eqb arga argb &&  builtin_eqb fa fb && pointwise dla dlb
        | _, _ => false
      end%bool . 
  
  (** The actual implementation of cse on expressions. Recall that
  expressions are in a 3-adress code like representation (that is, all
  intermediate expressions have been flattened). 

  We start with expressions where variables are a pair of Var (an
  abstract representation of variables) and a symbolic value (of type
  [sval]). Each such expression is split into two parts: a regular
  expression (with variables in Var), and potentially a symbolic
  values (for values that can be represented).  *)

  Definition cse_expr t (e : expr Phi V t) : expr Phi Var t * option (sval t). 
  refine (
      match e  with
        | Einput t v => (Einput _ _ _ v, !!)
        (* | Eread t v => (Eread _ _ t v, Some (SRead t v))  *)
        | Evar t v => (Evar (fst v), Some (snd v)) 
        | Eread t v => (Eread v, !!)
        | Eread_rf n t v adr =>   (Eread_rf v (fst adr), !! )
        | Ebuiltin args res f x => let v := DList.map (fun x dx => fst dx) x in 
                                    let sv  := DList.map (fun x dx => snd dx) x in             
                                      (Ebuiltin f v ,  Some (SBuiltin f sv) ) 
        | Econstant ty c =>  (Econstant c, Some (SConstant _ c)) 
        | Emux t c l r =>                          
            if sval_eqb (snd l) (snd r) 
            then
              (Evar (fst l), Some (snd l))
            else 
              (
                Emux (fst c) (fst l) (fst r),              
                Some (SMux _ (snd c) (snd l) (snd r) )
              ) 
        | Efst l t x => (Efst (fst x), 
                        match snd x in sval t' return fstT t' with
                          | @STuple (_ :: _) dl => Some  (DList.hd  dl)
                          | _ => !!
                        end)
        | Esnd l t x => (Esnd  (fst x), 
                        match snd x in sval t' return sndT t' with
                          | @STuple (t::q) dl => Some  (@STuple q (DList.tl  dl))
                          | _ => !!
                        end)
        | Enth l t m x => (Enth  m (fst x), 
                          match snd x in sval t' return nthT  t' t 
                          with
                            | @STuple l dl => fun m => Some (DList.get  m dl)
                            | _ => fun _ => !!
                          end m) 
        | Etuple l exprs => let x := DList.map (fun x dx => fst dx) exprs in 
                            let y := DList.map (fun x dx => snd dx) exprs in 
                             (Etuple  x, Some (STuple  y))
      end). 

  Defined. 

    
    
  
  Definition Env : Type := list ({t : type & ((sval t * Var t) : Type )%type}). 

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
                  if sval_eqb sv sv' 
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
                | telescope_bind arg b cont => 
                    let (e,svo) := cse_expr arg b in 
                      match svo with 
                        | None => k :- e; 
                            let sv := (SVar arg (List.length F)) in
                            let F := add arg sv k F in
                              cse F (cont (k,sv))
                        | Some sv =>                   
                            match lookup arg sv F with 
                              | None =>     
                                  k :-  e; 
                                  let F := add arg  sv k F in
                                    cse F (cont (k,sv))
                              | Some old => cse F (cont (old, sv))
                            end
                      end
              end in cse E T). 
  Defined. 


  Definition cse_effect := (fun (a : sync) (x : (option ∘ effect V) a) =>
            match x with
              | Some x0 =>
                  match x0 in (effect _ s) return ((option ∘ effect Var) s) with
                    | effect_reg_write t x1 x2 =>
                        Some (effect_reg_write Var t (fst x1) (fst x2))
                    | effect_regfile_write n t x1 x2 x3 =>
                        Some (effect_regfile_write Var n t (fst x1) (fst x2) (fst x3))
                  end
              | None => !!
            end). 
  Definition cse_effects (eff: effects Phi V) : effects Phi Var :=
    DList.map cse_effect eff. 
  
  
  Definition cse_block  t (b : block Phi V t) : block Phi Var t :=    
    k :-- cse_telescope empty b;
    match k with (v,g,e) =>
                   & (fst v, fst g, cse_effects  e)
    end. 
End t. 

Notation V := (fun t => (eval_type t * sval  t))%type.  



(* Ltac d := *)
(*   match goal with *)
(*    H : context [do _ <- ?x; _] |- _ => *)
(*      let A := fresh in *)
(*      case_eq x; [intros ?X A | intros A]; rewrite A in H; simpl in H *)
(*   | |- context [do _ <- ?x; _] => *)
(*      case_eq x; intros; simpl *)
(*   end. *)

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

Definition lift (env : Env eval_type) : list ({t : type & eval_type t}) :=
  List.map (fun x => match x with  existT t (sv,v) => existT _ t v end) env. 

Require Seq. 
Class Gamma_inv (G : Gamma eval_type V) (E : Env eval_type) :=
  {
    Gamma_inv_1 : forall t (x : eval_type t) y, G |= x -- y -> x = fst y;
    Gamma_inv_2 : forall t (x: eval_type t) y, G |= x -- y -> eval_sval (lift E) (snd y)  = Some x;
    Gamma_inv_3 : forall t x sv, Seq.In (existT _ t (sv , x))  E -> G |= x -- (x,sv)
  }. 
 
Hint Resolve Gamma_inv_1 Gamma_inv_2 Gamma_inv_3. 

Lemma Gamma_inv_2' G E (H : Gamma_inv G E) : 
  forall t (x: eval_type t) y y', G |= x -- (y,y') -> eval_sval (lift E) y'  = Some x. 
Proof. 
  intros. change (y') with (snd (y,y')). eauto. 
Qed. 

Hint Resolve Gamma_inv_2'.

Ltac use :=
  match goal with 
    | H : Some _ = None |- _ => discriminate
    | H : None = Some _ |- _ => discriminate
    | H : ?G |= ?x -- ?y |- context [?x] =>
        rewrite (Gamma_inv_1 _ _ _ H) 
    | H : ?G |= ?x -- ?y, 
      H' : eval_sval _ (snd ?y) = Some ?z |- context [?z] =>
        progress 
          (assert (x = z) by (pose proof (Gamma_inv_2 _ _ _ H); congruence);
           subst)          
    | H : ?G |= ?x -- ?y, 
      H' : eval_sval _ (snd ?y) = None |- context [?z] =>
        pose proof (Gamma_inv_2 _ _ _ H); congruence
    | H : ?G |= ?x -- ?y |- context [eval_sval _ (snd ?y)] =>
        let p := fresh in 
          assert ( p := Gamma_inv_2 _ _ _ H);
        simpl in p;
        rewrite p;
        clear p
    | H : Some _ = Some _ |- _ => injection H; intros; subst; clear H
    | H : ?x = ?x |- _ => clear H
  end. 

Ltac save :=
  repeat match goal with 
           | H : _ |= _ -- _ |- _ => 
             pose proof (Gamma_inv_1 _ _ _ H);
             pose proof (Gamma_inv_2 _ _ _ H);
               clear H
         end. 


Arguments Gamma_inv_1  {G E} _ {t x y} _.
Arguments Gamma_inv_2  {G E} _ {t x y} _.
Arguments Gamma_inv_3  {G E} _ {t x sv} _.

   

Lemma type_cast_eq t (e : eval_type t) : type_cast t e = Some e. 
Proof. 
  unfold type_cast.
  generalize (type_eqb_correct t t). intros. 
  generalize (type_eqb_refl t). 
  destruct (type_eqb t t). 
  
  rewrite (UIP_refl _ _ (e0 eq_refl)).  
  simpl. reflexivity. 
  discriminate. 
Qed. 

Require Import Equality. 

Lemma sval_eqb_correct t (sv sv' : sval t) : sval_eqb  sv sv' = true -> sv = sv'. 
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
  - apply var_eqb_correct_2 in H. subst. reflexivity. 
  - revert H.
    rewrite type_cast_eq. 
    intros. apply type_eq_correct in H.  congruence. 
  - repeat match goal with 
      | H : forall t, _ -> _ , H' : _ |- _ => apply H in H'; clear H; rewrite H'
  end. reflexivity.
  - induction l; DList.inv. reflexivity.   
    simpl in *. rewrite Bool.andb_true_iff in H0. destruct H0.
    repeat f_equal. 
    destruct H. auto. 
    destruct H. specialize (IHl _ H2 _ H1). clear - IHl. injection IHl; intros; injectT; auto. 
  - pose proof (type_list_eqb_correct  _ _ H0); subst. 
    clear H0. 
    apply builtin_eqb_correct in H2; subst. 
    f_equal. 
    clear f. induction t. DList.inv. reflexivity. 
    DList.inv. rewrite Bool.andb_true_iff in H1. destruct H1.  f_equal.   
    simpl in H. intuition.  apply IHt. simpl in H; intuition. auto. 
Qed. 

Lemma cse_expr_correct : forall t e1 r1, 
  eval_expr Phi st t e1 = r1 ->
  forall G (env : Env eval_type) e2,
    expr_equiv _ _ Phi (R G) t e1 e2 ->     
    Gamma_inv G env
    -> match snd (cse_expr _ t  e2) with
        | Some sv => eval_sval ( lift env) sv  = Some r1
        | None => True
      end.
Proof. 
  destruct 1; inversion 1; injectT;  try solve [simpl; auto]; intros. 
  - simpl. clear X. intro_do x Hx.  repeat f_equal.      
    {
      revert Hx. clear f. 
      induction args; simpl; DList.inv. 
      + simpl;   congruence. 
      + simpl in *. intro_do hd Hhd; try discriminate; intro_do tl Htl; try discriminate.   
        intros H; injection H; intros; subst; clear H. 
        specialize (IHargs _ _ p _ Htl). clear Htl. rewrite IHargs; clear IHargs. 
        f_equal. eapply Gamma_inv_2 in i; eauto. congruence. 
    }
    
    { exfalso. 
      clear f. 
      induction args; DList.inv; simpl in *.
      +  discriminate. 
      + simpl_do. 
        eapply Gamma_inv_2 in i; eauto. congruence.  
        eauto. 
    }
  - intros. simpl.
    case_eq (sval_eqb (snd l2) (snd r2)). 
    * intros H'. simpl. 
      assert (r1 = l1). apply sval_eqb_correct in H'. 
      save. congruence.  
      subst; destruct c1; save; congruence. 
    * intros. simpl. repeat use; simpl. reflexivity. 
      
  - intros.  simpl. 
    destruct dl2 as [hd tl].  simpl.
    dependent destruction tl ; try tauto.
    save. subst. simpl in *. DList.inv. simpl_do. auto. 
  - intros. repeat use. simpl.  
    destruct dl2 as [hd tl].  simpl. dependent destruction tl; try tauto.
    save. subst. simpl in *. DList.inv. simpl_do. auto. 
  - intros. simpl.  
    destruct dl2 as [hd tl]. simpl.  dependent destruction tl; try tauto.
    clear X.
    save; simpl in *; simpl_do; subst. 

    induction v; DList.inv; simpl in *; simpl_do; eauto.          
  - simpl. repeat  use.  clear X.  
    induction l; DList.inv. 
    + reflexivity.
    + simpl in *.      
      eapply IHl in p. clear IHl.  repeat use. simpl. rewrite p.  reflexivity. 
Qed. 


 
Lemma lem1  env G  t e1 e2 e'  sv : 
  expr_equiv eval_type V Phi (RTL.R eval_type V G) t e1 e2 ->
  Gamma_inv G env ->
  cse_expr eval_type t e2 = (e', Some sv) ->
  eval_sval   (lift env) sv = Some (eval_expr Phi st t e1). 
Proof. 
  intros H H1 H2.  
  pose (H' := cse_expr_correct  _ _ (eval_expr Phi st t e1) (refl_equal)). 
  specialize (H' G env e2 H H1). 
  rewrite H2 in H'.
  apply H'. 
Qed.



Lemma lookup_1 env t (sv : sval t) e :
  lookup eval_type t sv (env) = Some e ->
  Seq.In (existT _ t (sv,e)) (env). 
Proof.
  intros. 
  induction env. discriminate.
  destruct a as [t' [sv' x']]. simpl in H.
  revert H. generalize (type_eqb_correct t' t). destruct (type_eqb t' t).  simpl. intros.
  pose proof (e0 eq_refl). subst. 

  case_eq (sval_eqb sv sv'); intros.    
  injectT. rewrite H0 in H.  apply sval_eqb_correct in H0. subst. inject H. apply Seq.In_cons. 
  rewrite H0 in H. apply Seq.In_skip. auto. 
  intros. apply Seq.In_skip.  auto. 
Qed. 

Lemma lem2  G env t e1 e2 sv : 
  Seq.In (existT _ t (sv,e2)) (env) ->
  Gamma_inv G env ->
  eval_sval  (lift env) sv = Some e1 ->
  G |= e1 -- (e2, sv). 
Proof. 
  intros. 
  
  apply (Gamma_inv_3 X0) in X. 
  pose proof (Gamma_inv_2 X0 X). 
  simpl in H0. 
  
  assert ( e1 = e2). congruence.
  subst; auto. 
Qed. 

Lemma lemma_2 env G  t e1 e2 e3 e'  sv : 
  expr_equiv eval_type V Phi (RTL.R eval_type V G) t e1 e2 ->
  Gamma_inv G env ->
  cse_expr eval_type t e2 = (e', Some sv) ->
  lookup eval_type t sv (env) = Some e3 ->
  eval_expr Phi st t e1 = e3. 
Proof. 
  intros. 
  assert (eval_sval (lift env) sv = Some (eval_expr Phi st t e1)). eauto using lem1.
  
  apply lookup_1 in H0.   
  apply (Gamma_inv_3  X0) in H0. 
  apply (Gamma_inv_2  X0) in H0. 
  simpl in *. congruence. 
Qed. 

Lemma Gamma_inv_cons G env t e sv : 
  Gamma_inv G env ->
  eval_sval (lift env) sv  = Some e ->
  Gamma_inv (cons eval_type V t e (e,sv) G) env. 
Proof. 
  intros. constructor. 
  - intros ty x y. inversion 1;injectT. reflexivity. eauto. 
  - intros ty x y. inversion 1;injectT. simpl. eauto.  eauto. 
  - intros. apply In_skip. eauto. 
Qed. 

Lemma nth_error_app {A} l :
  forall l' n (x : A), List.nth_error l n = Some x ->
                  List.nth_error (l ++ l') n = Some x. 
Proof. 
  induction l; destruct n; simpl; intuition. 
  discriminate. 
  discriminate. 
Qed.

Lemma eval_sval_monotone  l l' t (x: eval_type t) : 
  forall sv,  
    eval_sval l sv  = Some x  ->
    eval_sval (l ++ l')  sv = Some x. 
Proof. 
  Ltac crush := repeat match goal with 
    | H : context [(do _ <- _; _) = _] |- _ => invert_do H
    | |- context [do _ <- ?x ; _ ]  => case_eq x; intros; simpl
    | H : { _ : _ & _} |- _ => destruct H                                                      
    | H : List.nth_error ?l ?n = Some ?x, 
      H': List.nth_error (?l ++ ?l') ?n = Some ?y |- _ =>
        pose proof (nth_error_app l l' n x H);
        assert (x = y) by congruence;
        clear H H'; subst
    | H : List.nth_error ?l ?n = Some ?x, 
      H': List.nth_error (?l ++ ?l') ?n = None |- _ =>
        pose proof (nth_error_app l l' n x H);
        congruence
    | H : forall t, _ -> _ , H' : _ |- _ => apply H in H'; clear H
    | H : ?x = ?y , H' : ?x = ?z |- _ => 
        assert (y = z) by congruence; subst; try rewrite H, H'; clear H H'
    | H : Some ?x = Some ?y |- _ => injection H; clear H; intros; subst
    | |- Some _ = Some _ => f_equal
  end;  auto || (try congruence) .
  induction sv using sval_ind_alt; simpl; intuition; crush.

  injectT. 
  simpl. 
  auto. 
  - induction exprs; [intuition|inversion H; clear H];   intuition; crush. 

  - f_equal. clear f0. 
    induction args. simpl in *. clear; destruct x0; destruct o; reflexivity. 
    DList.inversion. simpl in *. crush; f_equal.  
    destruct H as [H _].  clear - H EQ1 EQ0.  crush. 
    destruct H as [_ H]. apply (IHargs _ H _ EQ _ EQ2). 

  - exfalso. clear f0. 
    induction args; DList.inv.
    discriminate.
    destruct H as [H H']. specialize (IHargs _  H'). clear H'.  
    invert_do EQ. rewrite (H _ EQ0 )  in H0. simpl in *. specialize (IHargs _ EQ). clear EQ. 
    apply IHargs. clear IHargs.
    invert_do H0; auto. discriminate. 
Qed. 


Lemma nth_error_map {A B} {f : A -> B} l t  :
  List.nth_error (List.map f (l ++ [t])) (List.length l) = Some (f t). 
Proof. 
  induction l. reflexivity. 
  simpl. auto. 
Qed.

(* Lemma list_in_snoc {} l (x y : A) : List.In x (l++[y]) -> ((List.In x l) + (x = y))%type.  *)
(* Proof. *)
(*   induction l. simpl; intuition. *)
(* Admitted.    *)


Lemma Gamma_inv_cons_var G env (Hg : Gamma_inv  G env) t (e : eval_type t): 
      Gamma_inv (cons eval_type V t e (e, SVar t (Datatypes.length env)) G)
                (add eval_type t (SVar t (Datatypes.length env)) e env). 
Proof.
  intros. 
  constructor.
  - intros ty x y. inversion 1;injectT. reflexivity.  use; reflexivity.  
  - intros ty x y. inversion 1;injectT. simpl. unfold lift. unfold add. simpl. 
    rewrite nth_error_map. simpl.
    
    apply type_cast_eq.
    apply (Gamma_inv_2 Hg) in X0.
    unfold lift, add in *. 

    destruct y as [ y sv]. 
    rewrite List.map_app. 
    revert X0. clear X. 
    match goal with |- context [List.map ?f _] => set (F := f) end. 
    replace (List.length env) with (List.length (List.map F env)) by apply List.map_length.
    generalize (List.map F env).  intros. simpl. 
    clear F. simpl in X0.  
    apply eval_sval_monotone ; auto.    
    
    
  - intros ty x y H. unfold add in H.  apply Seq.In_app in H.  
    destruct H. apply In_skip. eauto. 
    inversion i. injectT. apply In_ok. congruence. congruence. inversion X. 
Qed.         
      
Lemma Gamma_inv_cons_other G env (Hg : Gamma_inv G env) t (e : eval_type t) sv: 
  eval_sval (lift env) sv = Some e ->
  Gamma_inv (cons eval_type V t e (e, sv) G)
            (add eval_type t sv e env). 
Proof. 
  constructor. 
  - intros ty x y. inversion 1; subst; injectT; subst. reflexivity.   eauto. 
  - intros ty x y. inversion 1; subst; injectT; subst. 
    simpl. unfold lift, add. rewrite List.map_app. apply eval_sval_monotone. apply H.
    simpl. unfold lift, add. rewrite List.map_app. apply eval_sval_monotone. eapply Gamma_inv_2; eauto. 
  - intros ty x sv' H0.
    unfold add in H0; apply Seq.In_app in H0. 
    destruct H0. apply In_skip. eauto.
    apply Seq.In_cons_inversion in i. destruct i. injectT. inject e0. apply In_ok; auto. 
    apply Seq.In_nil in i; tauto. 
Qed. 

Lemma Gamma_inv_empty : Gamma_inv  (nil _ _ ) (empty eval_type). 
Proof. 
  constructor. 
  + intros ty x y H; inversion H. 
  + intros ty x y H; inversion H. 
  + intros. simpl in X. apply Seq.In_nil in X. tauto. 
Qed. 


End s. 

Notation V := (fun t => (eval_type t * sval _  t))%type.  


Lemma cse_effects_correct (Phi : state) st Delta G e  (Hg : Gamma_inv Phi st G e):
  forall e1 e2 
  (H : effects_equiv eval_type V Phi (RTL.R eval_type V G) e1 e2), 
   eval_effects Phi st e1 Delta =
   eval_effects Phi st (cse_effects Phi eval_type e2) Delta. 
Proof. 
  intros e1 e2 H.
  apply DList.map3_map. 
  unfold effects_equiv in H. eapply DList.pointwise_map; [| apply H]. 
  
  clear H;simpl. intros t dt1 dt2 H v1 v2.  
  unfold R in *; inversion H; injectT; simpl; clear H; trivial; destruct v2; try reflexivity.
  rewrite (@Gamma_inv_1 _ _ _ _ Hg _ _ _ X);
  rewrite (@Gamma_inv_1 _ _ _ _ Hg _ _ _ X0); trivial. 
  rewrite (@Gamma_inv_1 _ _ _ _ Hg _ _ _ X);
  rewrite (@Gamma_inv_1 _ _ _ _ Hg _ _ _ X0);
  rewrite (@Gamma_inv_1 _ _ _ _ Hg _ _ _ X1); trivial. 
Qed.  

Lemma cse_expr_correct_2 Phi st G env (Hg : Gamma_inv Phi st G env) t:
  forall e1 e2, expr_equiv eval_type V Phi (RTL.R eval_type V G) t e1 e2 ->
           forall svo e, cse_expr Phi eval_type t e2 = (e,svo) ->
                           eval_expr Phi st t e1 = eval_expr Phi st t e. 
Proof.
  Ltac crush :=
    repeat (match goal with 
      | H: (_,_) = (_,_) |- _ => injection H; clear H; intros; subst
      | Hg : Gamma_inv _ _ _ _ ,  H : In _ _ _ ?x ?y _ |- context [?x] =>
        rewrite (Gamma_inv_1  _ _   _ _ _ H)
      | H : DList.T [] |- _ => DList.inversion 
      | H : DList.T (_ :: _) |- _  => DList.inversion 
      | H : DList.pointwise _ ( _ :: _) _ _ |- _ => apply DList.inversion_pointwise in H; destruct H
    end); try reflexivity; try f_equal. 
  intros e1. destruct e1; intros e2 H; inversion H; injectT; simpl; intros; unfold RTL.R in *; crush.
  
  - simpl. f_equal. 
    clear dependent b. 
    induction args; DList.inv;simpl; intuition. 
    crush.  eauto. 
  - case_eq (sval_eqb _  (snd l2) (snd r2)); intros H'; rewrite H' in H0.    
    + apply sval_eqb_correct in H'. crush. simpl.
            
      Ltac save :=
        repeat match goal with 
          | H : In _ _ _ _ _ _ |- _ =>
              pose proof (Gamma_inv_1 _ _ _ _ _ H);
              pose proof (Gamma_inv_2 _ _  _ _ _ H);
              clear H
      end. 

      save. destruct H'.  subst. assert (fst l2 = fst r2) by congruence. rewrite H0.  
      clear. match goal with |- context [ if ?x then _ else _] => destruct x; reflexivity end. 
    + crush. 
  - simpl. clear H. 
    induction l; DList.inv;simpl; intuition. 
    + crush. eauto. 
Qed. 

Lemma cse_telescope_correct (Phi: state) st t  Delta: 
     forall (b : RTL.block Phi eval_type t)
       (b': RTL.block Phi V t)
       (G : Gamma eval_type V),
       block_equiv eval_type V Phi t G b b' ->
       forall e,
       Gamma_inv Phi st G e
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
  induction 1; simpl; intros E INV. 
  Ltac crush ::=
    repeat (match goal with 
      | H: (_,_) = (_,_) |- _ => injection H; clear H; intros; subst
      | Hg : Gamma_inv _ _ _ _ ,  H : In _ _ _ ?x ?y _ |- context [?x] =>
        rewrite (Gamma_inv_1  _ _  _ _ _ H)
      | H : DList.T [] |- _ => DList.inversion 
      | H : DList.T (_ :: _) |- _  => DList.inversion 
      | H : DList.pointwise _ ( _ :: _) _ _ |- _ => apply DList.inversion_pointwise in H; destruct H
      | |- Some _ = Some _ => f_equal
      | |- (_,_) = (_,_) => f_equal
      | |- context [eval_type _] => simpl eval_type
    end); try reflexivity. 
  
  - crush. 
    match goal with |- context [check ?x; _] => destruct x; [|reflexivity]  end. 
    crush. eauto using cse_effects_correct.  
  -  case_eq (cse_expr Phi eval_type a e2); intros; simpl.  
    + destruct o. 
      case_eq (lookup Phi eval_type a s E); intros; simpl; apply H; clear H.  
      * assert (H' : eval_expr Phi st a e1 = e3) by eauto using lem1, lemma_2. 
        rewrite H'. apply Gamma_inv_cons; auto. subst. eauto using lem1. 
      * assert (H' : eval_expr Phi st a e1 = eval_expr Phi st a e0). 
        {
          pose proof H0; eapply lem1 in H0; eauto. 
          eapply cse_expr_correct_2; eauto. }
        rewrite H'. 
        assert (eval_sval Phi st (lift _ E) s  = Some (eval_expr Phi st a e1)) by eauto using lem1. 
        apply Gamma_inv_cons_other; eauto.        
        congruence. 
      * apply H. clear H.   
        assert (H' : eval_expr Phi st a e1 = eval_expr Phi st a e0) by 
                (eauto using cse_expr_correct_2). 
         rewrite H' in *. 
         generalize (eval_expr Phi st a e0); intros. 
         apply Gamma_inv_cons_var; auto.  
Qed. 


Theorem cse_correct Phi st t (b : Block Phi t) Delta : WF Phi t b -> 
  eval_block Phi st t (b _) Delta = eval_block Phi st t (cse_block Phi eval_type t (b _)) Delta. 
Proof. 
  intros.  
  eapply cse_telescope_correct; eauto using Gamma_inv_empty.  
Qed. 
  

Definition Compile Phi t (b : Block Phi t) : Block Phi t :=  
  fun V => cse_block Phi V t (b _). 

Theorem Compile_correct Phi t b (Hwf : WF Phi t b): forall st Delta,
  Eval Phi st t (Compile Phi t b) Delta =  Eval Phi st t b Delta. 
Proof. 
  unfold Eval. intros. unfold Compile. symmetry. apply cse_correct. auto. 
Qed. 

