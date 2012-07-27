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
  | SRead : forall t, Common.var Phi (Treg t) -> sval t
  | SConstant : forall t, constant t -> sval t
  | SMux : forall t, sval Tbool -> sval t -> sval t -> sval t
  | STuple : forall l, DList.T sval l ->  sval (Ttuple l)
  | SBuiltin : forall arg res (f : Core.builtin arg res), 
                 DList.T sval arg -> 
                 sval res. 

  Arguments STuple {l}%list _%dlist. 
  Arguments SBuiltin {arg res} f _%dlist. 
  
  Definition eval_sval t ( sv : sval t) (env : forall t, list (eval_type t) )  : option (eval_type t).
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
                  | SVar t n => List.nth_error (env t) n
                  | SRead t v => Some (Common.Tuple.get _ _ v st)
                  | SConstant t x => Some x
                  | SMux t c l r  => 
                      do c <- eval_sval _ c;
                      do l <- eval_sval _ l;
                      do r <- eval_sval _ r;
                      Some (if c then l else r)
                | STuple l x => 
                    fold _ x
                | SBuiltin arg res f x => 
                    do x <- _;
                    Some (builtin_denotation _ _ f x)
              end in eval_sval t sv).
  refine ((fix fold l (dl : DList.T _ l): option (eval_type_list l) :=
          match dl in DList.T _ l' return (option (eval_type_list l')) with 
                                       | [] => Some tt
                                       | t :: q => 
                                           do t <- eval_sval _ t;
                                           do q <- fold _ q;
                                           Some ((t,q))
          end%dlist) _ x). 
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
        | Eread t v => (Eread _ _ t v, Some (SRead t v))
        | Eread_rf n t v adr =>   (Eread_rf _ _ _  t v (fst adr), !! )
        | Ebuiltin args res f x => let v := DList.map (fun x dx => fst dx) x in 
                                   let sv  := DList.map (fun x dx => snd dx) x in                                    (Ebuiltin _ _ args res f v ,  Some (SBuiltin f sv) )
        | Econstant ty c => (Econstant _ _ _ c, Some (SConstant _ c))
        | Emux t c l r =>  (Emux _ _ _ (fst c) (fst l) (fst r), !!) 
        | Efst l t x => (Efst _ _ _ _ (fst x), 
                        match snd x in sval t' return fstT t' with
                          | @STuple (_ :: _) dl => Some  (DList.hd _ _ _ _ dl)
                          | _ => !!
                        end)
        | Esnd l t x => (Esnd _ _ _ _ (fst x), 
                        match snd x in sval t' return sndT t' with
                          | @STuple (t::q) dl => Some  (@STuple q (DList.tl _ _ _ _ dl))
                          | _ => !!
                        end)
        | Enth l t m x => (Enth _ _ _ _ m (fst x), 
                          match snd x in sval t' return nthT  t' t 
                          with
                            | @STuple l dl => fun m => Some (DList.get _ _ _ _ m dl)
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
                | SRead ta va, SRead tb vb => var_eqb va vb 
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
  
  Record Env := mk
    {
      content : forall t : type , list (sval t * Var t);
      next : nat              
    }. 

  Definition empty : Env := mk (fun _ => [])%list 0. 

  Definition lookup (t : type) (sv: sval t) (E : Env) : option (Var t).
  refine (let l := content E t in 
            let fix lookup sv l :=
                match l with 
                  | [] => None
                | (sv',x) :: b => if sval_eqb _ _ sv sv' then Some x else lookup sv b
                end%list in 
              lookup sv l                 
         ). 
  Defined.

  Definition add (t : type) (sv : sval t) (v : Var t) : Env -> Env. 
  intros E.  
  refine (mk _ _ ). 
  intros t'. 
  case_eq (type_eqb t t'). 
  intros. apply type_eqb_correct in H. subst. apply ((sv,v) :: content E t')%list.  
  intros _. apply (content E t'). 
  apply (S (next E)). 
  Defined. 

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
                  let sv := (SVar arg (next F)) in
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
  refine( Tuple.map _ Phi eff). 
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

Notation V := (fun t => (eval_type t * sval _ t))%type.  
Definition lift {Phi} : Env Phi eval_type -> (forall t, list (eval_type t)). 
intros. 
apply (List.map (@snd _ _) (content _ _ X t)). 
Defined. 

Ltac t :=   repeat match goal with 
                       H : existT _ _ _ = existT _ _ _ |- _ => apply Eqdep.EqdepTheory.inj_pair2 in H
                   end.
Notation "G |- x -- y" := (In _ _ _ x y G) (no associativity, at level 71). 

Notation R := (fun G t x y => In _ _ t x y G).  

Require Import Equality. 
Lemma cse_expr_correct Phi st : forall t e1 r1, 
  eval_expr Phi st t e1 = r1 ->
  forall G (env : Env Phi eval_type) e2,
    expr_equiv _ _ Phi (R G) t e1 e2 ->     
    (forall t (x : eval_type t) y, G |- x -- y -> x = fst y)  ->
    (forall t (x : eval_type t) y, G |- x -- y -> eval_sval Phi st t (snd y) (lift env) = Some x)
    -> match snd (cse_expr Phi _ t  e2) with
        | Some sv => eval_sval Phi st t sv (lift env) = Some r1
        | None => True
      end.
Proof. 
  destruct 1; inversion 1; t; subst; try solve [simpl; auto].  
  - admit. 
  - intros.  simpl. 
    destruct dl2 as [hd tl].  simpl. dependent destruction tl; try tauto.    
    erewrite <- H1. 
    Focus 2.
    
    simpl in dl1. simpl in hd.  destruct dl1. simpl. 
    
    Lemma inversion_dlist {A F} : forall (t : A) q (dl : DList.T F (t :: q)), 
                                exists hd tl, dl = (hd :: tl)%dlist. 
    Admitted. 
    destruct (inversion_dlist _ _ t0) as [t01 [t02 H''] ]. subst. 
    pose (H'' := H1 _ _ _ H3). clearbody H''. simpl in H''. 
    repeat match goal with 
        H : context [do _ <- ?x; _] |- _ => destruct x; simpl in H
    end. 
    injection H''. intros; subst. 
Admitted. 
(*
    match goal with 
        |- context [do _ <- ?x; _] => 
          assert (x = Some (DList.to_tuple (fun x X => X) t))
    end. 
  clear H0. 
  induction dl2.  simpl.
  clear. assert (t = DList.nil). 
  Require Import Equality. dependent destruction t. reflexivity. 
  rewrite H. simpl. reflexivity. simpl. 
  Ltac d := (match goal with 
              |- context [do _ <- ?x; _] => case_eq x; intros; simpl
          end). 
  d. d.
  f_equal. dependent destruction t. simpl.
  f_equal. 

  simpl. 
  simpl. 
  

  inversion t. 
  

  
 
Theorem cse_correct Phi st t  Delta: 
     forall (b : block Phi eval_type t)
     (b' : block Phi V t)
     (e : Env Phi eval_type)
     (G : Gamma eval_type V),
       block_equiv eval_type V Phi t G b b' ->
     (forall t (x : eval_type t) y, G |- x -- y -> x = fst y)  ->
     (forall t (x : eval_type t) y, G |- x -- y -> eval_sval Phi st t (snd y) (lift e) = Some x)
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
  simpl. intros. admit. 
  simpl. intros. 
  case_eq (cse_expr Phi eval_type a e2). intros. 
  destruct o. simpl. 
  case_eq (lookup Phi eval_type a s e). intros.
  apply H1. clear H1. 
  
  assert (eval_expr Phi st a e0 = eval_expr Phi st a e1). 
  admit. 
  rewrite <- H1. 
  
  forall G b b', 
    Flat.block_equiv _ _ Phi t G  b b' -> 
    Flat.eval_block Phi st t b Delta = Flat.eval_block Phi st t (cse_block Phi _ t b') Delta.      
Proof.  
  unfold eval_block. unfold cse_block. 
  generalize (empty Phi eval_type).
  
  intros e b b' H. revert e.  revert b b' H. induction 1. 
  
  simpl. intros.  
  subst. simpl.  
  repeat match goal with 
             |- context [check ?x ; _] => destruct x
         end; try reflexivity.
  subst. 
  f_equal. f_equal.
  admit.

  simpl. 
  case_eq (cse_expr Phi eval_type a e2). 
  intros e o Heo env. 
  case_eq o. simpl. intros. subst. simpl.
  case_eq (lookup Phi eval_type a s env).  intros.
  erewrite <- H1. 
  reflexivity. 
  clear H1 . 
  clear H0. 
  simpl. 


  Lemma lemma Phi st t sv env e : lookup Phi eval_type t sv env = Some e -> 
              eval_sval Phi st t sv (lift Phi (content _ _ env)) = Some e. 
  Proof. 
  Admitted.
  
  Lemma cse_expr_correct Phi st t env e e' e'' sv : cse_expr Phi eval_type t e = (e', Some sv) -> 
                             eval_sval Phi st t sv env = Some e'' -> 
                             eval_expr Phi st t e' = e''. 
  Admitted.
pose (h' := Heo). 
eapply cse_expr_correct in h'.
2 : apply lemma.  2: apply H2. 
erewrite cse_expr_correct. 
eapply cse_expr_correct. apply Heo.  eauto. 

  intros.  simpl. erewrite <- H1.  reflexivity. 
  admit. 
  
  intros. subst.  
  simpl. erewrite <- H1. reflexivity. 
  admit. 
Qed. *)