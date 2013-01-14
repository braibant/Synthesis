Require Import Common. 
Require Import DList. 
Require Import Core.   
Require Import Front. 
  
Section t. 
  Variable Phi : state. 
  Notation updates := (DList.T (option ∘ eval_mem) Phi). 
  
  Section defs. 
  Variable R : type -> Type. 
  (** Combinational bindings (expressions, register reads)  *)
  Inductive bind (t : type) : Type := 
  | bind_expr :  expr R t ->  bind t
  | bind_reg_read : var Phi (Treg t) -> bind t
  | bind_input_read : var Phi (Tinput t) -> bind t
  | bind_regfile_read : forall n, var Phi (Tregfile n t) -> R (Tint n) -> bind t. 
    
  Inductive telescope (A : Type): Type :=
  | telescope_end : A -> telescope A
  | telescope_bind : forall arg, bind arg -> (R arg -> telescope A) -> telescope A. 
    
  (* nested effects *)
  Inductive neffect  : Type :=
  | neffect_guard : forall (guard : expr R Tbool), list (neffect) -> neffect 
  | neffect_reg_write : forall t, var Phi (Treg t) -> R t -> neffect
  | neffect_regfile_write : forall n t, var Phi (Tregfile n t) -> R ( (Tint n)) -> R t -> neffect. 

  Definition nblock t := telescope (R t * expr R Tbool * list neffect)%type. 
  
  Fixpoint compose {A B}
                   (tA : telescope  A)
                   (f : A -> telescope  B) :
    telescope  B :=
    match tA with
      | telescope_end e => f e
      | telescope_bind arg b cont => telescope_bind _  arg b (fun x => compose (cont x) f)
    end.

  Definition compose_block {t B} 
                           (tA : nblock t)
                           (f : R t -> expr R Tbool -> list neffect -> telescope B) :
    telescope B :=
    compose tA (fun x => match x with ((r,g),e) => f r g e end). 

  Hint Unfold compose_block. 
  Notation "x <- e1 ; e2" := (telescope_bind _ _ e1 (fun x => e2)) (right associativity, at level 80, e1 at next level).  
  Notation " & e " := (telescope_end _ e) (at level 71). 
  Notation "[< r , g , e >] :- t1 ; t2 " := (compose_block t1 (fun r g e => t2)) (right associativity, at level 80, t1 at next level). 
  
  Arguments neffect_guard guard%expr neffects%list. 
  
  (** * Compilation *)
  (** This 'smart constructor' reduces the size of the guard, by using
  the fact that [true] is a neutral element for [&&] *)
  
  Definition andb (a b : expr R Tbool): expr R Tbool :=
    match a, b with 
      | Econstant Tbool x, o 
      | o, Econstant Tbool x => if x then o else (#b false)%expr
      | _, _ => (a && b)%expr
    end. 
  

  Definition orb (a b : expr R Tbool): expr R Tbool :=
    match a, b with 
      | Econstant Tbool x, o 
      | o, Econstant Tbool x => if x then (#b true) else o
      | _, _ => (a || b)%expr
    end. 
  
  Definition convert  l : DList.T (expr R) l -> Tuple.of_list (expr R) l := 
    DList.to_tuple (fun t X => X). 

  (**  The compilation function itself *)  
  Definition compile_inner (unit : R Tunit) t (a : action Phi R t) : telescope (R t * expr R Tbool * list neffect).  
  refine (
      let f := fix compile t (a : action Phi R t) : telescope (R t * expr R Tbool * list neffect):= 
          match a with 
            | Return t exp =>  
                x <- (bind_expr _ exp); 
                & (x, #b true, nil)
            | Bind t u A F => 
                [< rA, gA, eA >] :- compile _ A;
                [< rB, gB, eB >] :- compile _ (F rA); 
                & (rB, andb gA gB, List.app eA eB)             
            | Assert exp => 
                x <- (bind_expr _ exp); 
                & (unit, Evar x, nil)%expr
            | Primitive args res p exprs => _
            | OrElse t A A' => 
                [< rA, gA, eA >] :- compile _ A;
                [< rA', gA', eA' >] :- compile _ A';
                let e := neffect_guard gA eA in 
                let e' := neffect_guard (andb (~ gA)  gA')%expr eA' in 
                  r <- (bind_expr _ (Emux gA (Evar rA) (Evar rA'))%expr); 
                  & ( r , (orb gA gA')%expr , [e;e'])%list
          end in f t a).
  refine (match p in primitive _ args res return DList.T (expr R) args -> 
                                                  telescope (R res * expr R B * list neffect)         
          with
            | input_read t v => fun _ => x <- bind_input_read _ v; &(x, #b true, nil)
            | register_read t v => fun _ => x <- (bind_reg_read _ v); &(x, #b true, nil) 
            | register_write t v => fun exprs =>
                                     let env := convert _ exprs in
                                     let w := fst env in
                                     x <- bind_expr _ w;
                                     let e := ([neffect_reg_write _ v x])%list  in
                                     &( unit, #b true, e)
            | regfile_read n t v  => fun exprs =>
                                       let env := convert _ exprs in
                                       let adr := fst env in
                                       adr <- bind_expr _ adr;
                                       x <- bind_regfile_read _ _ v adr;
                                       &( x, #b true, nil)
            | regfile_write n t v  => fun exprs =>
                                       let env := convert _ exprs in
                                       match env with
                                         | (adr, (w, _)) =>
                                           adr <- bind_expr _ adr;
                                         w <- bind_expr _ w;
                                         let e :=  ([neffect_regfile_write _ _ v  adr w])%list in
                                         &(unit, #b true, e)
                                       end
          end exprs). 
  Defined. 
    
  (* At this point, we take the opportunity to introduce several
  extraneous bindings, that may end up being useful in ulterior steps,
  namely the boolean optimisation and the common-sub-expression
  elimination.  *)

  Definition compile t a :=   
    (unit <- (bind_expr _ (# Ctt))%expr; 
     _ <- bind_expr _ (#b true)%expr;
     _ <- bind_expr _ (#b false)%expr;
     compile_inner unit t a). 
  
  
  Inductive effect  : mem -> Type :=
  | effect_reg_write : forall t,  R t -> R Tbool -> effect (Treg t)
  | effect_regfile_write : forall n t,  R t -> R ( (Tint n)) -> R Tbool -> 
                                                effect (Tregfile n t). 
  
  Definition effects := DList.T (option ∘ effect) Phi. 
  
  Definition init_effects : effects := @DList.init mem (option ∘ effect) (fun t : mem => None) Phi. 

  Definition block t := telescope (R t * expr R Tbool *  effects). 
    
  Notation "e :-- t1 ; t2 " := (compose t1 (fun e => t2)) (right associativity, at level 80, e1 at next level).
  Arguments Tuple.set {T F l t} _ _ _.  

  Definition nblock_to_block {t} (B : nblock t) : block t. 
  unfold block, nblock in *. 
  
  Definition inversion_effect_Treg t (e : effect (Treg t)) : (R t * R Tbool) :=
    match e with 
      | effect_reg_write _ x y => (x,y)
    end. 

  Definition inversion_effect_Tregfile t n (e: effect (Tregfile n t)): 
    (R t * R ( (Tint n)) *R Tbool) :=
    match e with 
      | effect_regfile_write _ _ x y z => (x,y,z)
    end. 

  Definition merge s (a b : effect s) : telescope (option (effect s)). 
  refine (match s as s'  return effect s' -> effect s' -> telescope (option (effect s')) with 
              | Tinput t => fun a b => & None
              | Treg t => fun a b => 
                           let (va,ga) := inversion_effect_Treg t a in 
                           let (vb,gb) := inversion_effect_Treg t b in 
                             (
                               we <- bind_expr  _ (Evar ga || Evar gb)%expr ;
                               w <- bind_expr  _ (Emux  (Evar ga) (Evar va) (Evar vb) )%expr ;
                               & (Some (effect_reg_write  _ w we)))
              | Tregfile n t => fun a b => 
                           match inversion_effect_Tregfile t n a with 
                             | (va,adra,ga) =>
                                 match inversion_effect_Tregfile t n b with 
                                   | (vb,adrb,gb) =>
                                       (
                                         we <- bind_expr  _ (orb (Evar ga) (Evar gb))%expr; 
                                         wadr <- bind_expr _ (Emux (Evar ga) (Evar adra) (Evar adrb))%expr; 
                                         wdata <- bind_expr _ (Emux (Evar ga) (Evar va) (Evar vb))%expr; 
                                         &  (Some (effect_regfile_write _ _ wdata wadr we)))
                                 end
                           end
          end a b). 
  Defined. 

    (** We give the priority to the old write here  *)
  Definition update t (v : var Phi t) (e : effect t)  (acc: effects) : telescope effects. 
  refine ( match DList.get  v acc with 
               | Some old => 
                   e :-- merge t old e ; & (DList.set v e acc)
               | None => 
                   & (DList.set v (Some e) acc)
           end). 
  Defined. 
                                                                       

  Fixpoint compile_neffect (G : expr R Tbool) (E : neffect) (B : effects) : telescope effects :=
    match E with               
      | neffect_guard guard L => 
                    let compile_neffects := fix compile_neffects G l U :=
                        match l with 
                          | nil =>  & U
                          | cons t q => 
                              compose (compile_neffect G t U)
                                      (compile_neffects G q)
                        end in 
                      compile_neffects (andb G  guard)%expr L B
      | neffect_reg_write t v val => 
          G <- bind_expr _  G;
          update (Treg t) v (effect_reg_write t val G) B
      | neffect_regfile_write n t v adr val => 
          G <- bind_expr _  G;
          update (Tregfile n t) v (effect_regfile_write n t val adr G) B
    end.  

    
  Fixpoint compile_neffects (G : expr R Tbool)(l : list neffect)  (T : effects) :
    telescope effects :=
    match l with 
      | nil =>  & T
      | cons t q => 
          compose (compile_neffect G  t T)
                  (compile_neffects G q)
    end. 

  refine (compose_block B (fun res guard neffects => 
                             compose (compile_neffects (guard ) neffects (init_effects))
                             (fun effects => &(res, guard, effects)))). 
  Defined. 


  End defs. 
  
  (** * Semantics *)
  Section sem. 
    Variable st : eval_state Phi. 
    Definition eval_bind t (b : bind eval_type t) : (eval_type t).
    refine (match b with
              | bind_expr x =>  (eval_expr _ x)
              | bind_reg_read v => (DList.get v st)
              | bind_input_read v => (DList.get v st)
              | bind_regfile_read n v adr => 
                  let rf := DList.get  v st in
                    Regfile.get rf (adr)                
            end
           ). 
    Defined. 
    
                                                                
    Fixpoint eval_neffect (e :neffect eval_type) (Delta : updates) : updates :=    
      match e with 
        | neffect_guard g l' => 
            let fix eval_neffects l Delta := 
                match l with 
                  | nil => Delta
                  | cons e q =>  
                      let Delta := eval_neffect e Delta in 
                        eval_neffects q Delta
                end in     
              match eval_expr _ g with 
                | true => 
                    eval_neffects l' Delta
                | false => Delta
            end
      | neffect_reg_write t v w =>                                               
          Front.Diff.add Phi Delta (Treg t) v w 
      | neffect_regfile_write  n t v adr w  =>  
          let rf := DList.get v st in                          
            let rf := Regfile.set rf adr  w in 
              Front.Diff.add Phi Delta (Tregfile n t) v rf            
    end. 
  
    Fixpoint eval_neffects ( l : list (neffect eval_type)) Delta : updates :=
      match l with 
        | nil =>  Delta
        | cons e q => (* do Delta <- eval_neffect e Delta;  *)
            let Delta :=  (eval_neffect e Delta) in 
            eval_neffects q Delta
      end. 
  
    Lemma fold_eval_neffects :
      (fix eval_neffects l Delta := 
       match l with 
                | nil =>  Delta
                | cons e q => 
                    let Delta := (eval_neffect e Delta) in 
                      (* do Delta <- eval_neffect e Delta;  *)
                      eval_neffects q Delta
       end)= eval_neffects .
    Proof. 
      unfold eval_neffects. reflexivity.
    Qed. 
    
    Fixpoint eval_nblock t  (T : nblock  eval_type t) :
      updates -> option (eval_type t * updates) := 
      match T with
        | telescope_bind arg bind cont => 
            fun Delta => 
              let res := eval_bind _ bind in
              eval_nblock _ (cont res) Delta
        | telescope_end (p, g, e) => fun Delta =>
                                      let g := eval_expr _ g  in             
                                      if g then                                         
                                        Some (p, eval_neffects e Delta)
                                      else None
    end. 
    
    
    Arguments Tuple.set {T F l t} v _ _. 
    Definition eval_effects (e : effects eval_type) (Delta : updates) : updates.  
    unfold effects in e. 

    (* refine (Tuple.fold Phi _ e Delta).  *)
    refine (DList.map3 _ Phi e st Delta). 

    Definition eval_effect (a : mem) :   
      (option ∘ effect eval_type) a ->
      eval_mem a -> (option ∘ eval_mem) a -> (option ∘ eval_mem) a. 
    
    refine (fun  eff => 
              match eff with 
                  | Some eff =>  
                      match eff in effect _ s return eval_mem s -> (option ∘ eval_mem) s -> (option ∘ eval_mem) s  with 
                        |  effect_reg_write t val we =>  fun _ old => 
                             match old with 
                               | Some _ => old
                               | None => if we then Some val else None
                             end
                        |  effect_regfile_write n t val adr we => fun rf old =>
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

    Fixpoint eval_block t  (T : block eval_type t) :
      updates -> option (eval_type t * updates) := 
      match T with
        | telescope_bind arg bind cont => 
            fun Delta => 
              let res := eval_bind _ bind in
              eval_block _ (cont res) Delta
        | telescope_end (p, g, e) => fun Delta =>
                                      let g := eval_expr _ g  in             
                                      if g then                                         
                                        Some (p, eval_effects e Delta)
                                      else None
    end. 
  
     
  End sem. 
  
  Section correctness. 
  
    
    Notation C := (compile_inner eval_type tt). 
    Lemma eval_andb_true x y : (eval_expr Tbool (andb eval_type x y)) = (eval_expr Tbool x && eval_expr Tbool y)%bool.
    Proof. 
      Import Equality Bool. 
      
      dependent destruction x; dependent destruction y; simpl;
      repeat match goal with 
                 c : constant B |- _ => destruct c
               | x : eval_type Tbool |- _ => destruct x
               | _ => idtac
             end; rewrite ?andb_true_r, ?andb_true_l, ?andb_false_l , ?andb_false_r ; reflexivity.  
    Qed. 

    Lemma eval_orb_true x y : (eval_expr Tbool (orb eval_type x y)) = (eval_expr Tbool x || eval_expr Tbool y)%bool.
    Proof. 
      Import Equality Bool. 
      
      dependent destruction x; dependent destruction y; simpl;
      repeat match goal with 
                 c : constant B |- _ => destruct c
               | x : eval_type Tbool |- _ => destruct x
               | _ => idtac
             end; rewrite ?orb_true_r, ?orb_true_l, ?orb_false_l , ?orb_false_r ; reflexivity.  
    Qed. 


    Lemma eval_neffects_append  st e f (Delta : updates) : 
      eval_neffects st (e ++ f) Delta = 
                   eval_neffects st f (eval_neffects st e Delta).              
    Proof. 
      revert Delta. 
      induction e. 
      + reflexivity. 
      + intros Delta.
        
        simpl. rewrite IHe. reflexivity.  
    Qed. 

    Variable st : eval_state Phi. 

    Notation "B / Delta " := (eval_nblock st _ B Delta). 
    Theorem compile_correct t (a : action Phi eval_type t)  Delta:
      eval_nblock st _ (C t a ) Delta =  (Front.Sem.eval_action a st Delta).
    Proof. 
      revert Delta. 
      induction a. 
      - intros.  reflexivity. 
      - intros Delta. simpl. unfold  Sem.Dyn.Bind. rewrite <- IHa.
        transitivity (
            do ed <- (C t a) / Delta ; 
            let (e,d) := ed in 
              eval_nblock st u (C u (f e)) d
                   ); 
        [|destruct  ((C t a) / Delta) as [[ e d ]| ]; simpl; easy]. 
        clear IHa H.
        generalize (C t a) as T. intros T. clear a.
        
        induction T. destruct a as [[rA gA] eA]. 
        simpl in *. 
        case_eq (eval_expr Tbool gA); intros H.  simpl.
        unfold compose_block; simpl compose.  
        induction (C u (f rA)). simpl. destruct a as [[rB gB] eB]. simpl. 
        * rewrite eval_neffects_append. rewrite eval_andb_true. rewrite H. simpl. reflexivity. 
        * simpl. rewrite H0. reflexivity.         

        * unfold compose_block. simpl. induction (C u (f rA)). destruct a as [[rB gB] eB]. simpl. 
          rewrite eval_andb_true. rewrite H. reflexivity.  
          simpl. rewrite H0. reflexivity. 
        * unfold compose_block. simpl. unfold compose_block in H. rewrite H. reflexivity.

      - simpl. intros. 
          Ltac t :=
            repeat match goal with 
                     | |- context [check ?x ; ?y] => 
                         let H := fresh "check" in 
                           case_eq x; intros H
                   end. 
          t; trivial. 
      -                         (* primitive *)
      intros. destruct p.  
        +  simpl. reflexivity. 
        +  simpl. reflexivity. 
        + simpl.
              
          set (x := DList.to_tuple eval_expr exprs). 
          replace (x) with (fst x, snd x) by (destruct x; reflexivity).
          simpl.
          DList.inversion. simpl. reflexivity. 

        + simpl. 
          DList.inversion; reflexivity.
        + simpl. repeat DList.inversion. simpl. reflexivity.
          Arguments andb R _ _ : simpl never. 
          Arguments orb R _ _ : simpl never. 
          Ltac s :=
            match goal with 
              |- context [eval_expr _ (orb _ ?x ?y )] => rewrite eval_orb_true
            | |- context [eval_expr _ (andb _ ?x ?y )] => rewrite eval_andb_true
            | H : context [eval_expr _ (orb _ ?x ?y )] |- _ => rewrite eval_orb_true in H
            | H : context [eval_expr _ (andb _ ?x ?y )] |- _  => rewrite eval_andb_true in H
            | H : eval_expr _ ?x = true |- context [eval_expr _ ?x] => rewrite H
            | H : eval_expr _ ?x = true , H' : context [eval_expr _ ?x] |- _ => rewrite H in H'
            | H : eval_expr _ ?x = false |- context [eval_expr _ ?x] => rewrite H
            | H : eval_expr _ ?x = false , H' : context [eval_expr _ ?x] |- _ => rewrite H in H'
            end. 
      - intros. simpl.   unfold Sem.Dyn.OrElse. 
        rewrite <- IHa1, <- IHa2 . clear IHa1 IHa2. 
        generalize (C t a1); intros T; generalize (C t a2); intros T'. 
        induction T as [[[rA gA] eA] |]; simpl.
        induction T' as [[[rA' gA'] eA'] |]. simpl compose.
        t. simpl. repeat (s; simpl). reflexivity. 
        t. simpl. repeat (s; simpl). t. reflexivity. 
        reflexivity. 
        simpl. unfold compose_block in *. simpl in *.  rewrite H. reflexivity. 
        simpl. unfold compose_block in *. simpl in *.  rewrite H. reflexivity. 

    Qed.
     
  End correctness.     
 End t. 

Section correctness2. 
  
  Notation Cs  := (compile_neffects  _ _).
  Notation C  := (compile_neffect  _ _).
  Notation "x <- e1 ; e2" := (@telescope_bind _ _ _ _ _ e1 (fun x => e2)) (right associativity, at level 80, e1 at next level).
  Notation " & e " := (@telescope_end _ _ _ e) (at level 71).
  Notation "e :- t1 ; t2 " := (@compose  _ _ _ _ t1 (fun e => t2)) (right associativity, at level 80, t1 at next level).

  

  Ltac t := simpl; intuition; try match goal with
                                    | [ H : _ |- _ ] => rewrite H; auto
                                end.
   
  
  Lemma eval_effect_init Phi st Delta : eval_effects Phi st (init_effects Phi eval_type) Delta = Delta. 
  Proof.
    unfold eval_effects. 
    induction Phi. simpl. reflexivity. 
    simpl. repeat DList.inversion. simpl. f_equal. apply IHPhi. 
  Qed. 

  Lemma foo {Phi R A B C} (T: telescope Phi R A) (f : A -> telescope  Phi R B)  (g : B -> telescope Phi R C) :
    (X :- (Y :- T; f Y); (g X) )= (Y :- T; X :- f Y; g X).
  Proof.
      induction T. reflexivity. simpl.
      f_equal.
      Require Import  FunctionalExtensionality.
      apply functional_extensionality.
      apply H.
  Qed.
     
  Lemma my_ind Phi (R : type -> Type) (P : neffect Phi R -> Prop) :
    (forall (guard : expr R Tbool) ,
       P (neffect_guard Phi  R guard [])) ->
    (forall (guard : expr R Tbool) a l ,
       P a -> P (neffect_guard Phi  R guard l) ->
       P (neffect_guard Phi  R guard (a :: l))) ->
    (forall (t : type) (v : var Phi (Treg t)) (r : R t),
       P (neffect_reg_write  Phi R t v r)) ->
    (forall (n : nat) (t : type) (v : var Phi (Tregfile n t))
       (r : R ( (Tint n))) (r0 : R t),
       P (neffect_regfile_write Phi R n t v r r0)) ->
    forall n : neffect Phi R, P n. 
  Proof.
    intros. 
    refine (let fold := fix fold n :=
        match n with
            | neffect_guard g l => 
                let fix foldi l : P (neffect_guard Phi R g l) :=
                    match l return  P (neffect_guard Phi R g l) with 
                      | nil => H g
                      | cons t q => H0 g t q (fold t) (foldi q)
                    end in foldi l
            | neffect_reg_write t v w => H1 t v w
            | neffect_regfile_write n t v adr w => H2 n t v adr w
        end in fold n). 
  Qed. 
  
  Lemma correspondance Phi l e : forall g1 g2, 
                               compile_neffect Phi eval_type g1 (neffect_guard Phi eval_type g2 l) e = (compile_neffects Phi eval_type (andb _ g1  g2)%expr l e).
  Proof.                                                                                        
    induction l; reflexivity.
  Qed. 
  
  Lemma eval_neffect_cons Phi st guard a l Delta: 
    eval_neffect Phi st (neffect_guard Phi eval_type guard (a :: l)) Delta = 
                 (if eval_expr Tbool guard
                  then eval_neffects Phi st l (eval_neffect Phi st a Delta)
                  else Delta).
  Proof. 
    reflexivity. 
  Qed.
  
  Fixpoint eval_telescope { A B} Phi st (F : A -> B) (T : telescope  Phi eval_type A) :=
    match T with 
      | telescope_end X => F X
      | telescope_bind arg bind cont =>
          let res := eval_bind Phi st arg bind in 
            eval_telescope Phi st F (cont res)
    end. 

  Lemma folder Phi st guard l Delta: eval_neffect Phi st (neffect_guard  Phi eval_type guard l) Delta 
                                         = if eval_expr Tbool guard then eval_neffects Phi st l Delta else Delta.
  Proof. 
    reflexivity. 
  Qed. 
    

  
  Notation "[[ x ]]" := (eval_expr Tbool x). 
  Arguments Tuple.set {T F l t} _ _ _.
  Arguments Tuple.get {T F l t} _ _. 

  Notation Ev Phi st  := (eval_telescope Phi st (eval_effects Phi st)).  
  
  Ltac v := match goal with 
                |- context [match ?X with  | ( _ , _  )  => _ end ] => destruct X 
            end. 
  Import Equality. 
  Ltac d := match goal with 
              | H : context [match ?X with | _ => _ end] |- _ => dependent destruction X
              |  |- context [match ?X with | _ => _ end] => case_eq  X; intros; subst; simpl
                                                                                      
            end. 

  Lemma rew_1 Phi st Delta t (v : var Phi t ) x e : 
    eval_effects Phi st (DList.set v (Some x) e) Delta =
                 DList.set v (eval_effect t (Some x) (DList.get v st) (DList.get v Delta))  (eval_effects Phi st e Delta).  
  Proof. 
    induction Phi; [dependent destruction v|]. 
    dependent destruction v. 
    simpl; repeat v; destruct x; simpl; d; f_equal.
    simpl. repeat v; destruct x; simpl; rewrite IHPhi; clear IHPhi; 
           simpl; repeat d; simpl in *; auto. 
  Qed. 

  Lemma inversion_1 Phi st : forall t (v : var Phi (Treg t)) e Delta x x', 
                             inversion_effect_Treg eval_type t x = (x', true) ->
                             DList.get v e = Some x ->
                             exists y, DList.get v (eval_effects Phi st e Delta) = Some y.
  Proof. 
    induction Phi; [dependent destruction v|]. 
    dependent destruction v; simpl; intros. 
    repeat v; dependent destruction x; simpl in *; inversion H; subst; clear H; simpl.
    repeat DList.inversion.  simpl in H0. subst. simpl.
    d; eauto.

    simpl in *. repeat v. simpl. edestruct IHPhi; eauto.
  Qed. 


  Lemma compile_effect_correct Phi st a  : 
    forall Delta e g , 
      eval_telescope Phi st (eval_effects Phi st) (C g a e) Delta 
                     =  if [[g]] then eval_neffect Phi st a (Ev Phi st (&e) Delta) else (Ev Phi st (&e)Delta). 
  Proof. 
      induction a using my_ind. 
      - intros. simpl. destruct ([[guard]]); destruct ([[g]]); reflexivity.
      - intros. rewrite correspondance. rewrite eval_neffect_cons. 
        simpl compile_neffects. simpl.
        setoid_rewrite correspondance in IHa0.
        
        revert IHa IHa0.
        intros H. specialize (H Delta e (andb _ g guard)%expr). revert H. 
        induction (C (andb _ g guard)%expr a e); intros. 
        {simpl. rewrite IHa0. rewrite folder. simpl. simpl in H. rewrite eval_andb_true in H.        simpl in H. 
         destruct ([[g]]); destruct ([[guard]]); simpl; simpl in H; try rewrite H; try reflexivity. }
         {
         simpl. rewrite H. reflexivity. 
         simpl. simpl in *. rewrite H0. reflexivity.
         apply IHa0.          
         }
      - intros. simpl.
        unfold update. 
        case_eq (DList.get  v e); intros; simpl. 
        +               
        (* case: there was a previous effect on this register *)
        case_eq (inversion_effect_Treg eval_type t e0); intros; simpl.       
          
        
        rewrite rew_1. 
        case_eq (e2); intros; simpl. 
          * destruct ([[g]]). 
            subst. 
            {
              Lemma hint_1 Phi : forall st t (v : var Phi (Treg t)) r Delta e  e0, 
                                 DList.get v e = Some e0 -> 
                                 forall e1, inversion_effect_Treg eval_type t e0 = (e1, true) -> 
                                       DList.set v
                                            match DList.get v Delta with
                                                | Some _ => DList.get v Delta
                                                | None => Some e1
              end (eval_effects Phi st e Delta) =
                                          Diff.add Phi (eval_effects Phi st e Delta) (Treg t) v r. 
              Proof. 
                
                induction Phi; [dependent destruction v|].
                simpl. intros; repeat v. 
                 dependent destruction v; simpl; intros. 
                 repeat DList.inversion.  
                 unfold Diff.add;  simpl; repeat d; simpl in *; subst;
                 simpl in H1; dependent destruction e0; f_equal; auto.
                 discriminate. 
                 simpl in *; inversion H0; subst; auto. 
                 simpl in *; inversion H0; subst; discriminate.
                 simpl in *. setoid_rewrite IHPhi. unfold Diff.add.  simpl.
                 repeat d; reflexivity.
                 eauto. 
                 eauto. 
              Qed.
            eapply hint_1; eauto. 
            }
            subst.
            {
              induction Phi; [dependent destruction v|]. 
              simpl; repeat v. 
              dependent destruction v; simpl in *; subst. unfold Diff.add.
               unfold effects in *.  repeat DList.inversion. simpl in *.
              repeat d; clear IHPhi; dependent destruction e0;subst; f_equal; auto. 
              simpl in H0. inversion H0; subst. auto.
              simpl. rewrite IHPhi. auto. auto. 
            }
         
            

          * subst.
            destruct ([[g]]). 
            simpl. 
            unfold Diff.add. 
            {
            induction Phi; [dependent destruction v|]. 
              simpl; repeat v. 
              dependent destruction v; simpl in *; subst. unfold Diff.add.
               unfold effects in *.  repeat DList.inversion. simpl in *.

              repeat d; clear IHPhi; dependent destruction e0;subst; f_equal; auto. 
              discriminate. simpl in *; inversion H0; subst; auto. 
              simpl in *; inversion H0; subst; auto. 
              discriminate.
              
              setoid_rewrite IHPhi. clear IHPhi. unfold Diff.add. simpl. d. reflexivity.
              reflexivity. 
              auto. 
            }
            
            {
            induction Phi; [dependent destruction v|]. 
              simpl; repeat v. 
              dependent destruction v; simpl in *; subst. unfold Diff.add.
               unfold effects in *.  repeat DList.inversion. simpl in *.

              repeat d; clear IHPhi; dependent destruction e0;subst; f_equal; auto. 
              simpl in *. inversion H0; auto. 
              
              setoid_rewrite IHPhi. auto.  auto. 
            
            }
            
            
            
        + rewrite rew_1. simpl. 

          unfold Diff.add. 
          {
          
            induction Phi; [dependent destruction v|]. 
              simpl; repeat v. 
              dependent destruction v; simpl in *; subst. unfold Diff.add.
               unfold effects in *.  repeat DList.inversion. simpl in *.
repeat d; repeat f_equal. 
              
              setoid_rewrite IHPhi. clear IHPhi. unfold Diff.add. simpl. repeat d; f_equal. auto. 
          }

      - intros. simpl.         unfold update. 
        case_eq (DList.get v e); intros; simpl. 
        +               
        case_eq (inversion_effect_Tregfile eval_type t n e0); intros [w adr we H']; simpl.         
        rewrite rew_1.
        simpl.
        case_eq (we); intros; simpl. 
        * destruct [[g]]. 
          unfold Diff.add.
          {
            induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst.
             unfold effects in *.  repeat DList.inversion. simpl in *; subst. 
            

            unfold Diff.add; repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi;  auto. 
            unfold Diff.add; repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
          }
          subst. 
          {
            induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst. 
             unfold effects in *.  repeat DList.inversion. simpl in *; subst. 

            unfold Diff.add; repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi;  auto. 
          }

          *destruct [[g]]. subst. 
          unfold Diff.add. 
          {
              induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst. 
                         unfold effects in *.  repeat DList.inversion. simpl in *; subst. 
unfold Diff.add; repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi;  auto. 
            repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.          
          }
          {
            induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst. unfold Diff.add.
                         unfold effects in *.  repeat DList.inversion. simpl in *; subst. 
repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi; auto. }
          
          
        + rewrite rew_1. simpl.
          unfold Diff.add. 
          {
            induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst. unfold Diff.add.
             unfold effects in *.  repeat DList.inversion. simpl in *; subst. 

            repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi; auto. 
            repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto. 

          }
    Qed. 

    Lemma eval_telescope_neffects Phi st es : forall Delta e g, eval_telescope Phi st (eval_effects Phi st) (Cs g es e) Delta 
                               =  if [[g]] then eval_neffects Phi st es (Ev Phi st (&e) Delta) else Ev Phi st (&e) Delta. 
    Proof. 
      induction es. 
      intros; simpl.  destruct ([[g]]); reflexivity.  
      simpl. intros. 
      pose (H := compile_effect_correct Phi st a Delta e g). 
      clearbody H. revert H. 
      induction (C g a e). 
      - simpl.       intros H. 
      rewrite IHes. simpl. rewrite H. destruct ([[g]]); reflexivity.
      - simpl. intros. apply H. simpl. auto.  
    Qed. 
 
    Theorem nblock_compile_correct Phi (st : eval_state Phi) t (nb : nblock Phi eval_type t)  Delta:
      eval_block Phi st _  (nblock_to_block Phi eval_type nb) Delta =  eval_nblock Phi st _ nb Delta. 
      unfold nblock in nb. 
      induction nb as [ [ [rA gA] eA]|]. 
      2: simpl; rewrite <- H; reflexivity. 
      
      {
        unfold nblock_to_block. unfold compose_block. simpl.
        pose (H := eval_telescope_neffects Phi st eA Delta (init_effects Phi eval_type) gA). 
        clearbody H. 
        case_eq ([[gA]]).
        {
          intros. rewrite H0 in H. simpl in H. 
          rewrite eval_effect_init in H. 
          rewrite <- H. clear H.  
          induction (Cs gA eA (init_effects Phi eval_type)). simpl. rewrite H0. reflexivity. 
          simpl. rewrite <- H. reflexivity. 
        }
        {
          intros.
          induction (Cs gA eA (init_effects Phi eval_type)). simpl. rewrite H0. reflexivity. 
          simpl. apply H1. auto.          
        }
      }

    Qed. 
  
End correctness2. 

Definition Block Phi t := forall V,  block Phi V t. 
Definition Compile Phi t (A : forall V, action Phi V t) : Block Phi t := 
  fun V =>
    nblock_to_block Phi V (compile Phi V t (A V)):block Phi V t. 

Definition Next Phi st t (B : Block Phi t) :=
  match eval_block Phi st t (B _) (Diff.init Phi) with 
    | None => None
    | Some Delta => Some (fst Delta, Diff.apply Phi (snd Delta) st)
  end. 


Theorem Compile_correct Phi t A : forall st,
  Next Phi st t (Compile Phi t A) =  Front.Next Phi st  A. 
Proof. 
  unfold Compile, Next, Front.Next. intros. 
  rewrite nblock_compile_correct. 
  simpl.  rewrite compile_correct. reflexivity.   
Qed. 

(*
Section equiv. 
  Import Core. 
  Variable U V : type -> Type. 
  Variable Phi : state. 

  Reserved Notation "x == y" (at level 70, no associativity). 
  Reserved Notation "x ==e y" (at level 70, no associativity). 
  
  Section inner_equiv. 
  Variable R : forall t, U t -> V t -> Type. 
  Notation "x -- y" := (R _ x y) (at level 70, no associativity). 
    
  Inductive expr_equiv : forall t,  expr U t -> expr  V t -> Prop :=
  | Eq_var : forall  t (v1 : U t) v2, v1 -- v2 -> Evar v1 == Evar v2
  | Eq_builtin : forall args res (f : builtin args res) dl1 dl2, 
                   DList.pointwise expr_equiv args dl1 dl2 ->
                   Ebuiltin  f dl1 == Ebuiltin  f dl2
  | Eq_constant : forall ty (c : constant ty), Econstant c == Econstant c
  | Eq_mux : forall t c1 c2 l1 l2 r1 r2, 
               c1 == c2 -> l1 == l2 -> r1 == r2 -> 
               @Emux  U t c1 l1 r1 ==  @Emux  V t c2 l2 r2
                    
  | Eq_fst : forall (l : list type) (t : type) dl1 dl2, 
               dl1 == dl2 -> 
               @Efst U l t dl1 == @Efst  V l t dl2

  | Eq_snd : forall (l : list type) (t : type) dl1 dl2, 
               dl1 == dl2 -> 
               @Esnd  U l t dl1 == @Esnd  V l t dl2

  | Eq_nth : forall (l : list type) (t : type) (v : Common.var l t)  dl1 dl2, 
               dl1 == dl2 -> 
               Enth v dl1 == Enth v dl2

  | Eq_tuple : forall (l : list type) dl1 dl2, 
                 DList.pointwise expr_equiv l dl1 dl2 ->
               @Etuple  U l dl1 == @Etuple  V l dl2
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
 
  Definition effects_equiv : effects Phi U -> effects Phi V -> Type := 
    DList.pointwise effect_equiv Phi. 
  
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

  Inductive bind_equiv t : forall (G : Gamma), bind Phi U t -> bind Phi V t -> Prop :=
  |Eq_expr : forall G v1 v2, expr_equiv (R G) t v1 v2 ->
                        bind_equiv t G (bind_expr Phi U t v1) (bind_expr Phi V t v2)
  |Eq_reg : forall G v, bind_equiv t G  (bind_reg_read Phi U t v) (bind_reg_read Phi V t v)
  |Eq_regfile : forall G n v a1 a2, 
                  G |- a1 -- a2 ->
                  bind_equiv t G  (bind_regfile_read Phi U t n v a1) (bind_regfile_read Phi V t n v a2). 

  Inductive block_equiv t : forall (G : Gamma), block Phi U t -> block Phi V t -> Prop :=
  | Eq_end : forall G (v1 : U t) v2 g1 g2 e1 e2, 
               G |- v1 -- v2 ->  expr_equiv (R G) _ g1 g2 -> effects_equiv (R G) e1 e2 ->
               G |- telescope_end Phi U _ (v1, g1, e1) ==b telescope_end Phi V _ (v2,g2, e2 ) 
  | Eq_bind : forall G a (e1 : bind Phi U a) e2 (k1 : U a -> block Phi U t) k2,
                bind_equiv _ G e1 e2 -> 
                (forall v1 v2, (* G |- v1 -- v2 ->  *)cons _ v1 v2 G |- k1 v1 ==b k2 v2) ->
                G |- telescope_bind Phi U _ a e1 k1 ==b telescope_bind Phi V _ a e2 k2                
                 where "G |- x ==b y" := (block_equiv _ G x y). 
End equiv. 

Definition WF Phi t (b : Block Phi t) := forall U V, block_equiv U V Phi t (nil _ _) (b _) (b _). 
*)