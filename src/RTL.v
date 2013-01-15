Require Import Common. 
Require Import DList. 
Require  Core Front IR Equality.

(** RTL language, with three address code.   *)

Section t. 
  Variable Phi : Core.state. 
  
  Notation updates := (DList.T (Common.comp option  Core.eval_mem) Phi). 
  
  Section defs. 
    Import Core. 
    Variable Var : type -> Type. 
    
    Inductive expr : type -> Type :=
    | Evar : forall t, Var t -> expr t
    | Einput : forall t, var Phi (Tinput t) -> expr t 
    | Eread : forall t,  var Phi (Treg t) -> expr t
    | Eread_rf : forall n t, var Phi (Tregfile n t) -> Var (Tint n) -> expr t 

    | Eandb : Var B -> Var B -> expr B
    | Eorb  : Var B -> Var B -> expr B
    | Exorb : Var B -> Var B -> expr B
    | Enegb : Var B -> expr B

    (* "type-class" *)
    | Eeq   : forall t, Var t -> Var t -> expr B

    (* integer operations *)                                          
    | Elt   : forall n, Var (Int n) -> Var (Int n) -> expr B
    | Ele   : forall n, Var (Int n) -> Var (Int n) -> expr B
    | Eadd  : forall n, Var (Int n) -> Var (Int n) -> expr (Int n)
    | Esub  : forall n, Var (Int n) -> Var (Int n) -> expr (Int n)
    | Elow  : forall n m, Var (Int (n + m)) -> expr (Int n)
    | Ehigh  : forall n m, Var (Int (n + m)) -> expr (Int m)
    | EcombineLH   : forall n m, Var (Int n) -> Var (Int m) -> expr (Int (n + m))

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
      
    Inductive effect  : mem -> Type :=
    | effect_reg_write : forall t,  Var t -> Var Tbool -> effect (Treg t)
    | effect_regfile_write : forall n t,  Var t -> Var (Tint n) -> Var Tbool -> 
                                     effect (Tregfile n t). 
    
    Definition effects := DList.T (option ∘ effect) Phi. 
    
    Definition block t := telescope (Var t * Var Tbool *  effects). 
    Notation ret x := (telescope_end _ x). 
    Notation " & e " := (telescope_bind _ _ e (fun x => ret x)) (at level 71). 
    Notation "x :- e1 ; e2" := (telescope_bind  _ _  e1 (fun x => e2)) (right associativity, at level 80, e1 at next level).  
    
    
    Fixpoint compile_expr t (e : Front.expr Var t) : telescope (Var t) :=
      match e with
        | Front.Evar t v => ret v
        | Front.Eandb a b => a :-- compile_expr _ a; 
                            b :-- compile_expr _ b; 
                            & (Eandb a b)
        | Front.Eorb a b => a :-- compile_expr _ a; 
                            b :-- compile_expr _ b; 
                            & (Eorb a b)
        | Front.Exorb a b => a :-- compile_expr _ a; 
                            b :-- compile_expr _ b; 
                            & (Exorb a b)
        | Front.Enegb a => a :-- compile_expr _ a; 
                          & (Enegb a)
        | Front.Eeq t a b => a :-- compile_expr _ a; 
                            b :-- compile_expr _ b; 
                            & (Eeq _ a b)
        | Front.Elt n a b => a :-- compile_expr _ a; 
                            b :-- compile_expr _ b; 
                            & (Elt _ a b) 
        | Front.Ele n a b => a :-- compile_expr _ a; 
                            b :-- compile_expr _ b; 
                            & (Ele _ a b)
        | Front.Eadd n a b => a :-- compile_expr _ a; 
                             b :-- compile_expr _ b; 
                             & (Eadd _ a b)
        | Front.Esub n a b => a :-- compile_expr _ a; 
                              b :-- compile_expr _ b; 
                              & (Esub _ a b)
        | Front.Elow n m a => a :-- compile_expr _ a; 
                             & (Elow n m a) 
        | Front.Ehigh n m a => a :-- compile_expr _ a; 
                              & (Ehigh n m a)
        | Front.EcombineLH n m a b  => a :-- compile_expr _ a; 
                                      b :-- compile_expr _ b;
                                      & (EcombineLH n m a b)
        | Front.Econstant ty c => & (Econstant _ c)
        | Front.Emux t c l r => 
            c :-- compile_expr _ c;
            l :-- compile_expr _ l;
            r :-- compile_expr _ r;
            & (Emux t c l r)
        | Front.Efst l t x => 
          x :-- compile_expr _ x; 
          & (Efst l t x)
        | Front.Esnd l t x => 
          x :-- compile_expr _ x; 
          & (Esnd l t x)
        | Front.Enth l t m x => 
          x :-- compile_expr _ x;
          & (Enth l t m x)
        | Front.Etuple l exprs => 
          let fix of_list 
                  (l : list type) 
                  (x : DList.T (Front.expr Var) l) : 
                telescope (DList.T Var l) :=
              match x in  (DList.T _ l)
                    return
                    (telescope (DList.T Var l)) with 
                | DList.nil => ret ([ :: ])%dlist
                | DList.cons t q dt dq => 
                  x  :-- compile_expr t dt;
                    dq :--   of_list q dq;   
                   ret (x :: dq)%dlist
              end in
                  
                  exprs :-- of_list l exprs; 
                & (Etuple l exprs)
      end.
    
    Fixpoint compile_exprs l (x: DList.T (Front.expr Var) l) :  telescope (DList.T Var l) :=
      match x in  (DList.T _ l)
         return
         (telescope (DList.T Var l)) with 
        | DList.nil => ret ([ :: ])%dlist
        | DList.cons t q dt dq => 
            x  :-- compile_expr t dt;
            dq :--   compile_exprs q dq;   
            ret  (x :: dq)%dlist
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
         | DList.nil => ret DList.nil
         | DList.cons t1 q0 dt dq =>
             x1 :-- compile_expr t1 dt;
             dq0 :-- of_list q0 dq; 
             ret (DList.cons x1 dq0)
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
                          (r, g,e) => g :-- compile_expr _ g; ret (r,g,compile_effects e)
                        end
                  | IR.telescope_bind a bd k => 
                      match bd with
                        | IR.bind_input_read v => 
                          x :- Einput a v; fold _ (k x)
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
    
    Definition eval_expr (t : Core.type) (e : expr Core.eval_type t) : Core.eval_type t:=
      match e with
        | Evar t v => v
        | Eread t v => (DList.get v st)
        | Einput t v => DList.get v st
        | Eread_rf n t v adr =>  
          let rf := DList.get  v st in
          Common.Regfile.get rf (adr)                
        | Eandb a b => andb a b 
        | Eorb a b =>  orb  a b
        | Exorb a b => xorb  a b
        | Enegb a => negb a
        | Eeq t a b => Core.type_eq t a b
        | Elt n a b => Word.lt a b
        | Ele n a b => Word.le a b
        | Eadd n a b => Word.add a b 
        | Esub n a b => Word.sub a b 
        | Elow n m a =>  Word.low n m a  
        | Ehigh n m a => Word.high n m a 
        | EcombineLH n m a b  =>  Word.combineLH n m  a b
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
      end. 
        
    Definition eval_effects (e : effects Core.eval_type) (Delta : updates) : updates.  
    unfold effects in e. 
    
    (* refine (DList.fold Phi _ e Delta).  *)
    refine (DList.map3 _ Phi e st Delta). 
    Import Common Core.
    Definition eval_effect (a : Core.mem) :   
      (Common.comp option (effect Core.eval_type)) a ->
      Core.eval_mem a -> (Common.comp option Core.eval_mem) a -> (Common.comp option Core.eval_mem) a. 
    
    refine (fun  eff => 
              match eff with 
                | Some eff =>  
                    match eff in effect _ s return eval_mem s -> (option ∘ eval_mem) s -> (option ∘ eval_mem) s  with 
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
      
      revert t e f . 

      fix IHe 2; destruct e; intros f; simpl; 
      repeat (match goal with 
                  |- context [ (_ :-- _ :-- _; _ ; _) ] => (rewrite foo; simpl)
                | |- context [_ :-- compile_expr _ _ ?t ?x; _] => rewrite (IHe t x)
                                                                        
             end); try reflexivity.       
      
      { simpl. rewrite (compile_exprs_fold Phi Core.eval_type). repeat rewrite foo; simpl.
        rewrite compile_exprs_correct.
        simpl; rewrite DList.map_to_tuple_commute. reflexivity. 
        
        clear f. induction exprs; simpl. auto.
        split. apply IHe. auto.  }  Qed. 
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
  Variable R : forall t, U t -> V t -> Type. 
  Notation "x -- y" := (R _ x y) (at level 70, no associativity). 
    
  Inductive expr_equiv : forall t,  expr Phi U t -> expr Phi V t -> Type :=
  | Eq_read : forall t v, Eread Phi U t v == Eread Phi V t v
  | Eq_read_rf : forall n t v adr1 adr2, 
                   adr1 -- adr2 -> 
                   Eread_rf Phi U n t v adr1 == Eread_rf Phi V n t v adr2
  | Eq_andb : forall a1 a2 b1 b2, a1 -- a2 -> b1 -- b2 -> 
                             Eandb Phi U a1 b1 == Eandb Phi V a2 b2
  | Eq_orb : forall a1 a2 b1 b2, a1 -- a2 -> b1 -- b2 -> 
                             Eorb Phi U a1 b1 == Eorb Phi V a2 b2
  | Eq_xorb : forall a1 a2 b1 b2, a1 -- a2 -> b1 -- b2 -> 
                             Exorb Phi U a1 b1 == Exorb Phi V a2 b2
  | Eq_negb : forall a1 a2, a1 -- a2 ->                       
                             Enegb Phi U a1 == Enegb Phi V a2
  | Eq_eq : forall t a1 a2 b1 b2, a1 -- a2 -> b1 -- b2 -> 
                             Eeq Phi U t a1 b1 == Eeq Phi V t a2 b2 
  | Eq_lt : forall n a1 a2 b1 b2, a1 -- a2 -> b1 -- b2 -> 
                             Elt Phi U n a1 b1 == Elt Phi V n a2 b2
  | Eq_add : forall n a1 a2 b1 b2, a1 -- a2 -> b1 -- b2 -> 
                             Eadd Phi U n a1 b1 == Eadd Phi V n a2 b2 
  | Eq_sub : forall n a1 a2 b1 b2, a1 -- a2 -> b1 -- b2 -> 
                              Esub Phi U n a1 b1 == Esub Phi V n a2 b2 
  | Eq_low : forall n m a1 a2,  a1 -- a2 -> 
                           Elow Phi U n m a1 == Elow Phi V n m a2
  | Eq_high : forall n m a1 a2,  a1 -- a2 -> 
                            Ehigh Phi U n m a1 == Ehigh Phi V n m a2
  | Eq_combineLH : forall n m a1 a2 b1 b2,  a1 -- a2 -> b1 -- b2 -> 
                            EcombineLH Phi U n m a1 b1 == EcombineLH Phi V n m a2 b2
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
  
  Inductive effect_equiv : forall t,  option (effect U t) -> option (effect V t) -> Type :=
  | Eq_none : forall t, effect_equiv t None None
  | Eq_write : forall t v1 v2 we1 we2, 
                 v1 -- v2 -> we1 -- we2 -> 
                 Some (effect_reg_write U t v1 we1) ==e Some  (effect_reg_write V t v2 we2)
  | Eq_write_rf : forall n t v1 v2 adr1 adr2 we1 we2, 
                    v1 -- v2 -> adr1 -- adr2 -> we1 -- we2 -> 
                    Some (effect_regfile_write U n t v1 adr1 we1) ==e 
                         Some (effect_regfile_write V n t v2 adr2 we2)
                                  where "x ==e y" := (effect_equiv _ x y). 
 
  Definition effects_equiv : effects Phi U -> effects Phi V -> Type := 
    DList.pointwise  effect_equiv Phi. 
    
  End inner_equiv. 
 
  Inductive Gamma : Type :=
  | nil : Gamma
  | cons : forall t, U t -> V t -> Gamma -> Gamma. 
  
  Inductive In t (x : U t) (y : V t) : Gamma -> Type :=
  | In_ok : forall Gamma x' y', x' = x -> y' = y ->
              In t x y (cons t x' y' Gamma )
  | In_skip : forall Gamma t' x' y', 
                In t x y Gamma -> 
                In t x y (cons t' x' y' Gamma ). 

  Definition R G := fun t x y => In t x y G.  

  Reserved Notation "G |- x ==b y" (at level 70, no associativity). 
  Notation "G |- x -- y" := (In _ x y G) (at level 70, no associativity). 

  Inductive block_equiv t : forall (G : Gamma), block Phi U t -> block Phi V t -> Type :=
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

Definition Next Phi st t (B : Block Phi t) :=
  match eval_block Phi st t (B _) (Front.Diff.init Phi) with 
    | None => None
    | Some Delta => Some (fst Delta, Front.Diff.apply Phi (snd Delta) st)
  end.


Theorem Compile_correct Phi t b st:
  Next Phi st t (Compile Phi t b) =  IR.Next Phi st t b. 
Proof. 
  unfold Next, Compile, IR.Next. intros. rewrite compile_correct. reflexivity.
Qed. 

Arguments Evar {Phi Var t} v. 
Arguments Eread {Phi Var t} v. 
Arguments Eread_rf {Phi Var n t} _ _ . 
Arguments Econstant {Phi Var ty} _. 
Arguments Emux {Phi Var t} _ _ _. 
Arguments Efst {Phi Var l t} _. 
Arguments Esnd {Phi Var l t} _. 
Arguments Enth {Phi Var l t} _ _. 
Arguments Etuple {Phi Var l} _%dlist. 
