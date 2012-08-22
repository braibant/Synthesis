Require Import Common. 
Require Import DList. 
Require  Core Front IR Equality.


Section t. 
  Variable Phi : Core.state. 
  
  Notation updates := (DList.T (Common.comp option  Core.eval_sync) Phi). 
  
  Section defs. 
    Import Core. 
    Variable Var : type -> Type. 
    
    Inductive expr : type -> Type :=
    | Evar : forall t, Var t -> expr t
    | Eread : forall t,  var Phi (Treg t) -> expr t
    | Eread_rf : forall n t, var Phi (Tregfile n t) -> Var (Tint n) -> expr t 
    | Ebuiltin : forall (args : list type) (res : type),
                   builtin args res ->
                   DList.T Var args ->
                   expr res
    | Econstant : forall ty : type, constant ty -> expr ty
    | Emux : forall t : type,
               Var Tbool ->  Var t -> Var t -> expr  t
    | Efst : forall (l : list type) (t : type),
               Var (Ttuple (t :: l)) -> expr t
    | Esnd : forall (l : list type) (t : type),
               Var (Ttuple (t :: l)) -> expr (Ttuple l)
    | Enth : forall (l : list type) (t : type),
               var l t -> Var (Ttuple l) -> expr t
    | Etuple : forall l : list type,
                 DList.T (Var) l -> expr  (Ttuple l). 
        
    Inductive telescope (A : Type): Type :=
    | telescope_end : A -> telescope A
    | telescope_bind : forall arg, expr arg -> (Var arg -> telescope A) -> telescope A. 
        
    Fixpoint compose {A B}
                     (tA : telescope  A)
                     (f : A -> telescope  B) :
      telescope  B :=
      match tA with
        | telescope_end e => f e
        | telescope_bind arg b cont => telescope_bind _  arg b (fun x => compose (cont x) f)
      end.
    Notation "e :-- t1 ; t2 " := (compose t1 (fun e => t2)) (right associativity, at level 80, e1 at next level).
      
    Inductive effect  : sync -> Type :=
    | effect_reg_write : forall t,  Var t -> Var Tbool -> effect (Treg t)
    | effect_regfile_write : forall n t,  Var t -> Var (Tint n) -> Var Tbool -> 
                                     effect (Tregfile n t). 
    
    Definition effects := DList.T (option ∘ effect) Phi. 
    
    Definition block t := telescope (Var t * Var Tbool *  effects). 
    Notation "x :- e1 ; e2" := (telescope_bind  _ _  e1 (fun x => e2)) (right associativity, at level 80, e1 at next level).  
    Notation " & e " := (telescope_end _  e) (at level 71). 
    
    
    Definition compile_expr t (e : Front.expr Var t) : telescope (Var t).
    refine (
        let fix fold t (e : Front.expr Var t) :=
            let fix of_list (l : list type) (x : DList.T (Front.expr Var) l) : telescope (DList.T Var l) :=
                match x in  (DList.T _ l)
                   return
                   (telescope (DList.T Var l)) with 
                      | DList.nil => & ([ :: ])%dlist
                      | DList.cons t q dt dq => 
                          x  :-- fold t dt;
                          dq :--   of_list q dq;   
                          &  (x :: dq)%dlist
                end in
              
              match e with
                | Front.Evar t v => & v
                | Front.Ebuiltin args res f x => 
                    x :-- of_list args x; 
                    y :- Ebuiltin args res f x; 
                    &y 
                | Front.Econstant ty c => c :- Econstant _ c; &c
                | Front.Emux t c l r => 
                    c :-- fold _ c;
                    l :-- fold _ l;
                    r :-- fold _ r;
                    ret :- (Emux t c l r) ;
                    & ret
                | Front.Efst l t x => 
                    x :-- fold _ x; ret :- Efst l t x; & ret
                | Front.Esnd l t x => 
                    x :-- fold _ x; ret :- Esnd l t x; & ret
                | Front.Enth l t m x => 
                    x :-- fold _ x; ret :- Enth l t m x; & ret
                | Front.Etuple l exprs => 
                    exprs :-- of_list l exprs; ret :- Etuple l exprs; &ret
              end in fold t e).
    Defined. 
    
    Fixpoint compile_exprs l (x: DList.T (Front.expr Var) l) :  telescope (DList.T Var l) :=
      match x in  (DList.T _ l)
         return
         (telescope (DList.T Var l)) with 
        | DList.nil => & ([ :: ])%dlist
        | DList.cons t q dt dq => 
            x  :-- compile_expr t dt;
            dq :--   compile_exprs q dq;   
            &  (x :: dq)%dlist
      end. 
    
    Lemma compile_exprs_fold : 
      (fix of_list (l : list Core.type)
           (x0 : DList.T
                       (Front.expr Var) l)
           {struct x0} :
       telescope 
                   (DList.T Var l) :=
       match
         x0 in (DList.T _ l0)
          return
          (telescope (DList.T Var l0))
       with
         | DList.nil => & DList.nil
         | DList.cons t1 q0 dt dq =>
             x1 :-- compile_expr t1 dt;
             dq0 :-- of_list q0 dq; & DList.cons x1 dq0
       end) = compile_exprs. 
    Proof. reflexivity. Qed. 
    
    Definition compile_effects (e : IR.effects Phi Var)  : effects. 
    unfold effects. refine  (DList.map _  e).
    intros a x.
    refine (match x with
              | None => None
              | Some x => match x with 
                           | IR.effect_reg_write t v g => 
                               Some (effect_reg_write t v g)
                           | IR.effect_regfile_write n t v adr g =>
                               Some (effect_regfile_write n t v adr g)
                         end
            end).
    
    Defined. 
    
    Definition compile t  (b : IR.block Phi Var t) : block t.     
    refine (let fold := fix fold t (b : IR.block Phi Var t) : block t :=
                match b with 
                  | IR.telescope_end x => 
                      match x with 
                          (r, g,e) => g :-- compile_expr _ g; & (r,g,compile_effects e)
                        end
                  | IR.telescope_bind a bd k => 
                      match bd with
                        | IR.bind_expr x => 
                            x :-- compile_expr _ x ; fold _ (k x)
                        | IR.bind_reg_read x => 
                            x :- Eread a x; fold _ (k x)
                        | IR.bind_regfile_read n x x0 => 
                            x :- Eread_rf n a x x0; fold _ (k x)
                      end
                end in fold t b                         
           ). 
      Defined. 
  End defs. 
  Section sem. 
    
    Variable st : Core.eval_state Phi. 
    
    Definition eval_expr (t : Core.type) (e : expr Core.eval_type t) : Core.eval_type t. 
    refine ( 
        let fix eval_expr t (e : expr Core.eval_type t) {struct e} : Core.eval_type t:=
            match e with
              | Evar t v => v
              | Eread t v => (DList.get v st)
              | Eread_rf n t v adr =>  
                  let rf := DList.get  v st in
                    Common.Regfile.get rf (adr)                

              | Ebuiltin args res f exprs => 
                  let exprs := 
                      DList.to_tuple  
                            (fun (x : Core.type) (X : Core.eval_type x) => X)
                            exprs
                  in
                    Core.builtin_denotation args res f exprs
              | Emux t b x y => if b then x else y 
              | Econstant ty c => c
              | Etuple l exprs => 
                  DList.to_tuple (fun _ X => X) exprs
              | Enth l t v e => 
                  Common.Tuple.get _ _ v e
              | Efst l t  e => 
                  Common.Tuple.fst e
              | Esnd l t  e => 
                  Common.Tuple.snd e
            end 
        in eval_expr t e).  
    Defined. 
        
    Definition eval_effects (e : effects Core.eval_type) (Delta : updates) : updates.  
    unfold effects in e. 
    
    (* refine (DList.fold Phi _ e Delta).  *)
    refine (DList.map3 _ Phi e st Delta). 
    Import Common Core.
    Definition eval_effect (a : Core.sync) :   
      (Common.comp option (effect Core.eval_type)) a ->
      Core.eval_sync a -> (Common.comp option Core.eval_sync) a -> (Common.comp option Core.eval_sync) a. 
    
    refine (fun  eff => 
              match eff with 
                | Some eff =>  
                    match eff in effect _ s return eval_sync s -> (option ∘ eval_sync) s -> (option ∘ eval_sync) s  with 
                      |  effect_reg_write t val we => 
                           fun _ old => 
                             match old with 
                               | Some _ => old
                               | None => if we then Some val else None
                             end
                      |  effect_regfile_write n t val adr we => 
                           fun rf old =>
                             match old with 
                               | Some _ => old 
                               | None => 
                                   if we then 
                                     let rf := Regfile.set rf adr val in 
                                       Some rf
                                   else 
                                     None                                       
                             end
                    end
                | None => fun _ old => old            
              end). 
    Defined. 
    apply eval_effect. 
    Defined. 
    
    Fixpoint eval_telescope { A B} (F : A -> B) (T : telescope  eval_type A) :=
      match T with 
        | telescope_end X => F X
        | telescope_bind arg bind cont =>
            let res := eval_expr arg bind in 
              eval_telescope F (cont res)
      end. 
    
    Definition eval_block  t  (T : block eval_type t) Delta :
      option (eval_type t * updates) := 
      eval_telescope (fun x => match x with (p,g,e)  =>
                                             if g : bool then                              
                                               Some (p, eval_effects e Delta)
                                             else None end) T. 
  End sem.
End t.  

Notation "e :-- t1 ; t2 " := (compose _ _  t1 (fun e => t2)) (right associativity, at level 80, e1 at next level).
Notation "x :- e1 ; e2" := (telescope_bind _ _ _ _ (e1) (fun x => e2)) (right associativity, at level 80, e1 at next level).  
Notation " & e " := (telescope_end _   _ _ e) (at level 71). 


Section correctness. 
  Import Equality.
  
  Lemma compile_effects_correct Phi st   e : 
    forall Delta, 
      eval_effects Phi st (compile_effects Phi Core.eval_type e) Delta =
                 IR.eval_effects Phi st e Delta. 
  Proof. 
    induction Phi. simpl. auto. 
    simpl; intros. unfold IR.effects in e. repeat DList.inversion. 
    case_eq c; intros; simpl; subst;
    destruct x1.
    dependent destruction e0. simpl. 
    rewrite IHPhi; reflexivity.
    simpl; f_equal; auto. 
    simpl; f_equal; auto. 
    simpl; f_equal; auto.
    destruct e. simpl. reflexivity.
    simpl. reflexivity. 
    simpl. f_equal. auto. 
  Qed. 
  
  Hint Resolve compile_effects_correct. 
  
  Lemma foo {Phi R A B C} (T: telescope Phi R A) (f : A -> telescope  Phi R B)  (g : B -> telescope Phi R C) :
    (X :-- (Y :-- T; f Y); (g X) )= (Y :-- T; X :-- f Y; g X).
  Proof.
    induction T. reflexivity. simpl.
    f_equal.
    Require Import  FunctionalExtensionality.
    apply functional_extensionality.
    apply H.
  Qed.
  
  
  Section compile_expr. 
    Context {A B : Type}. 
    Context {E : A -> B}.  
    Variable (Phi : Core.state) (st : Core.eval_state Phi). 
    Notation Ev := (eval_telescope Phi st E). 
    
    Section compile_exprs. 
      Notation P := (fun t e => 
                       forall  (f : Core.eval_type t -> telescope _ _ A), 
                         Ev(r :-- compile_expr Phi Core.eval_type t e; f r) = 
                           Ev (f (Front.eval_expr t e))). 
      Lemma compile_exprs_correct : forall l dl f,         
                                      DList.Forall P dl ->                    
                                      Ev (Y :-- compile_exprs Phi Core.eval_type l dl; f Y) =
                                         Ev (f (DList.map Front.eval_expr dl )). 
      Proof. 
        induction dl. simpl. reflexivity. 
        simpl. intros. rewrite foo. destruct H. rewrite H. rewrite foo. simpl. apply IHdl. auto. 
      Qed. 
    End compile_exprs. 
    Lemma compile_expr_correct t e (f : Core.eval_type t -> telescope _ _ A): 
      Ev (r :-- compile_expr Phi Core.eval_type t e; f r) = Ev (f (Front.eval_expr t e)). 
    Proof. 
      revert e.
      induction e using Front.expr_ind_alt; try reflexivity. 
      
      Ltac t :=
        match goal with 
            |- context [ (_ :-- _ :-- _; _ ; _) ] => rewrite foo
          | H : context [ _ :-- _ ; _ ] |- _ => rewrite H ; clear H
      end.
      
      { simpl. rewrite (compile_exprs_fold Phi Core.eval_type). repeat rewrite foo; simpl.
        rewrite compile_exprs_correct; auto.  simpl.  repeat f_equal. 
        rewrite DList.map_to_tuple_commute. reflexivity. }       
      
      {simpl; repeat t; reflexivity.   }
      {simpl; repeat t; reflexivity.   }
      {simpl; repeat t; reflexivity.   }
      {simpl; repeat t; reflexivity.   }
      
      { simpl. rewrite (compile_exprs_fold Phi Core.eval_type). repeat rewrite foo; simpl.
        rewrite compile_exprs_correct; auto.  simpl.  repeat f_equal.
        
        rewrite DList.map_to_tuple_commute. reflexivity. }       
    
    Qed. 
  End compile_expr. 
  
  Lemma compile_correct Phi st t (b : IR.block Phi Core.eval_type t) : 
    forall Delta, 
      eval_block Phi st t (compile Phi Core.eval_type t b) Delta = IR.eval_block Phi st t b Delta. 
  Proof. 
    intros.
    induction b.
    simpl. destruct a as [[r g] e]; simpl.
    unfold eval_block. 
    
    
    rewrite (compile_expr_correct Phi st Core.Tbool g). simpl. 
    destruct (Front.eval_expr Core.Tbool g); repeat f_equal.
    
    apply compile_effects_correct. 
    
    simpl. rewrite <- H. clear H. 
    unfold eval_block. destruct b; try reflexivity. 
    
    rewrite (compile_expr_correct Phi st arg e) . reflexivity.  
  Qed. 
End correctness. 


Section equiv. 
  Import Core. 
  Variable U V : type -> Type. 
  Variable Phi : state. 

  Reserved Notation "x == y" (at level 70, no associativity). 
  Reserved Notation "x ==e y" (at level 70, no associativity). 
  
  Section inner_equiv. 
  Variable R : forall t, U t -> V t -> Prop. 
  Notation "x -- y" := (R _ x y) (at level 70, no associativity). 
    
  Inductive expr_equiv : forall t,  expr Phi U t -> expr Phi V t -> Prop :=
  | Eq_read : forall t v, Eread Phi U t v == Eread Phi V t v
  | Eq_read_rf : forall n t v adr1 adr2, 
                   adr1 -- adr2 -> 
                   Eread_rf Phi U n t v adr1 == Eread_rf Phi V n t v adr2
  | Eq_builtin : forall args res (f : builtin args res) dl1 dl2, 
                   DList.pointwise R args dl1 dl2 ->
                   Ebuiltin Phi U args res f dl1 == Ebuiltin Phi V args res f dl2
  | Eq_constant : forall ty c, Econstant Phi U ty c == Econstant Phi V ty c
  | Eq_mux : forall t c1 c2 l1 l2 r1 r2, 
               c1 -- c2 -> l1 -- l2 -> r1 -- r2 -> 
               Emux Phi U t c1 l1 r1 ==  Emux Phi V t c2 l2 r2
                    
  | Eq_fst : forall (l : list type) (t : type) dl1 dl2, 
               dl1 -- dl2 -> 
               Efst Phi U l t dl1 == Efst Phi V l t dl2

  | Eq_snd : forall (l : list type) (t : type) dl1 dl2, 
               dl1 -- dl2 -> 
               Esnd Phi U l t dl1 == Esnd Phi V l t dl2

  | Eq_nth : forall (l : list type) (t : type) (v : Common.var l t)  dl1 dl2, 
               dl1 -- dl2 -> 
               Enth Phi U l t v dl1 == Enth Phi V l t v dl2

  | Eq_tuple : forall (l : list type) dl1 dl2, 
                 DList.pointwise R l dl1 dl2 ->
               Etuple Phi U l dl1 == Etuple Phi V l dl2
                            where "x == y" := (expr_equiv _ x y). 
  
  Inductive effect_equiv : forall t,  option (effect U t) -> option (effect V t) -> Prop :=
  | Eq_none : forall t, effect_equiv t None None
  | Eq_write : forall t v1 v2 we1 we2, 
                 v1 -- v2 -> we1 -- we2 -> 
                 Some (effect_reg_write U t v1 we1) ==e Some  (effect_reg_write V t v2 we2)
  | Eq_write_rf : forall n t v1 v2 adr1 adr2 we1 we2, 
                    v1 -- v2 -> adr1 -- adr2 -> we1 -- we2 -> 
                    Some (effect_regfile_write U n t v1 adr1 we1) ==e 
                         Some (effect_regfile_write V n t v2 adr2 we2)
                                  where "x ==e y" := (effect_equiv _ x y). 
 
  Definition effects_equiv : effects Phi U -> effects Phi V -> Prop := 
    DList.pointwise  effect_equiv Phi. 
    
  End inner_equiv. 
 
  Inductive Gamma : Type :=
  | nil : Gamma
  | cons : forall t, U t -> V t -> Gamma -> Gamma. 
  
  Inductive In t (x : U t) (y : V t) : Gamma -> Prop :=
  | In_ok : forall Gamma x' y', x' = x -> y' = y ->
              In t x y (cons t x' y' Gamma )
  | In_skip : forall Gamma t' x' y', 
                In t x y Gamma -> 
                In t x y (cons t' x' y' Gamma ). 

  Definition R G := fun t x y => In t x y G.  

  Reserved Notation "G |- x ==b y" (at level 70, no associativity). 
  Notation "G |- x -- y" := (In _ x y G) (at level 70, no associativity). 

  Inductive block_equiv t : forall (G : Gamma), block Phi U t -> block Phi V t -> Prop :=
  | Eq_end : forall G (v1 : U t) v2 g1 g2 e1 e2, 
               G |- v1 -- v2 -> G |- g1 -- g2 -> effects_equiv (R G) e1 e2 ->
               G |- telescope_end Phi U _ (v1, g1, e1) ==b telescope_end Phi V _ (v2,g2, e2 ) 
  | Eq_bind : forall G a (e1 : expr Phi U a) e2 (k1 : U a -> block Phi U t) k2,
                expr_equiv (R G) _ e1 e2 -> 
                (forall v1 v2, (* G |- v1 -- v2 ->  *)cons _ v1 v2 G |- k1 v1 ==b k2 v2) ->
                G |- telescope_bind Phi U _ a e1 k1 ==b telescope_bind Phi V _ a e2 k2                
                 where "G |- x ==b y" := (block_equiv _ G x y). 
End equiv. 

Definition Block Phi t := forall V, block Phi V t. 
Definition WF Phi t (b : Block Phi t) := forall U V, block_equiv U V Phi t (nil _ _) (b _) (b _). 
Definition Compile Phi t (B : IR.Block Phi t) : Block Phi t :=
  fun V => compile _ _ _ (B _).  
Definition Eval Phi st t (B : Block Phi t) Delta :=
  eval_block Phi st t (B _) Delta. 

Theorem Compile_correct Phi t b : forall st Delta,
  Eval Phi st t (Compile Phi t b) Delta =  IR.Eval Phi st t b Delta. 
Proof. 
  unfold Eval, Compile. intros. apply compile_correct.
Qed. 
(*
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

Theorem Compile_wf Phi t b : IR.WF Phi t b -> WF Phi t (Compile Phi t b). 
Proof. 
  unfold IR.WF, WF. 
  intros. specialize (H U V).
  unfold Compile.
  Record rel U V G G' :=
    {
      rel_1 :  (forall t v1 v2, IR.In U V t v1 v2 G -> In U V t v1 v2 G')
    }. 
  Hint Resolve rel_1. 
  Lemma compile_effects_wf Phi U V G  : 
    forall e1 e2,
      IR.effects_equiv U V Phi (fun t x y => IR.In U V t x y G) e1 e2 ->
      forall G', 
        rel U V G G' ->
        effects_equiv U V Phi (fun t x y => In U V t x y G') 
                      (compile_effects Phi U e1) (compile_effects Phi V e2). 
  Proof. 
  Admitted.
  Hint Resolve compile_effects_wf.
  Hint Unfold R. 
  Lemma compile_wf Phi U V G : forall  t b1 b2, 
                                 IR.block_equiv U V Phi t G b1 b2 ->
                                 forall G',
                                   rel U V G G' ->                                  
                                 block_equiv U V Phi t G' (compile Phi U t b1) (compile Phi V t b2). 
  Proof. 
    induction 1; simpl;  unfold IR.R, R in *. 
    
    - intros. inversion H0; t; simpl.
      constructor; eauto. eapply compile_effects_wf; eauto. 
      repeat rewrite foo. 
      unfold R. 
  
    simpl. 
    simpl. 
    
  inversion H. simpl. inversion H4;t; simpl.
  
  constructor; auto. 

  revert H. Import Equality. dependent induction b. induction H.
  
  simpl. 
 *)

Arguments Evar {Phi Var t} v. 
Arguments Eread {Phi Var t} v. 
Arguments Eread_rf {Phi Var n t} _ _ . 
Arguments Ebuiltin {Phi Var args res} _ _%dlist. 
Arguments Econstant {Phi Var ty} _. 
Arguments Emux {Phi Var t} _ _ _. 
Arguments Efst {Phi Var l t} _. 
Arguments Esnd {Phi Var l t} _. 
Arguments Enth {Phi Var l t} _ _. 
Arguments Etuple {Phi Var l} _%dlist. 
