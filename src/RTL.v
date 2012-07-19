Require Import Common. 
Require Import Core.   
  
Section t. 
  Variable Phi : state. 
  Notation updates := (Tuple.of_list (option ∘ eval_sync) Phi). 
  
  Section defs. 
  Variable R : type -> Type. 
  (** Combinational bindings (expressions, register reads)  *)
  Inductive bind (t : type) : Type := 
  | bind_expr :  expr R t ->  bind t
  | bind_reg_read : var Phi (Treg t) -> bind t
  | bind_regfile_read : forall n, var Phi (Tregfile n t) -> R (Tlift (Tfin n)) -> bind t. 
    
  Inductive telescope (A : Type): Type :=
  | telescope_end : A -> telescope A
  | telescope_bind : forall arg, bind arg -> (R arg -> telescope A) -> telescope A. 
    
  (* nested effects *)
  Inductive neffect  : Type :=
  | neffect_guard : forall (guard : expr R Bool), list (neffect) -> neffect 
  | neffect_reg_write : forall t, var Phi (Treg t) -> R t -> neffect
  | neffect_regfile_write : forall n t, var Phi (Tregfile n t) -> R (Tlift (Tfin n)) -> R t -> neffect. 

  Definition nblock t := telescope (R t * expr R Bool * list neffect)%type. 
  
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
                           (f : R t -> expr R Bool -> list neffect -> telescope B) :
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
  
  Definition andb (a b : expr R Bool): expr R Bool :=
    match a, b with 
      | Econstant Tbool x, o 
      | o, Econstant Tbool x => if x then o else (#b false)%expr
      | _, _ => (a && b)%expr
    end. 
    
  Definition convert  l : DList.T (expr R) l -> Tuple.of_list (expr R) l := 
    DList.to_tuple (fun t X => X). 

  Fixpoint map T F F' (G : forall t, F t -> F' t) (l : list T) : 
    Tuple.of_list F l -> Tuple.of_list F' l:=
    match l with 
      | nil => fun x => x
      | cons t q => fun x => (G t (fst x), map T F F' G q (snd x))
    end. 

  Arguments map {T F F'} G l _. 

  (**  The compilation function itself *)  
  Definition compile_inner (unit : R Unit) t (a : action Phi R t) : telescope (R t * expr R Bool * list neffect).  
  refine (
      let f := fix compile t (a : action Phi R t) : telescope (R t * expr R Bool * list neffect):= 
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
                & (unit, !x, nil)%expr
            | Primitive args res p exprs => _
            (* | Try A =>  *)
            (*     [< rA, gA, eA >] :- compile _ A; *)
            (*     let e := neffect_guard gA eA in *)
            (*       & (varunit, #b true, [e])%list *)
            (*     (* & (varunit, gA, eA) *) *)
            | OrElse t A A' => 
                [< rA, gA, eA >] :- compile _ A;
                [< rA', gA', eA' >] :- compile _ A';
                let e := neffect_guard gA eA in 
                let e' := neffect_guard ((~ gA) &&  gA')%expr eA' in 
                  r <- (bind_expr _ (Emux _ _ gA (!rA) (!rA'))%expr); 
                  & ( r , (gA || gA')%expr , [e;e'])%list
          end in f t a).
  (* primitive *)
  revert exprs. 
  refine (match p with
            | register_read t v => _
            | register_write t v => _
            | regfile_read n t v  => _
            | regfile_write n t v  => _
          end); clear p; intros exprs. 
  (* register read *)
  refine (x <- (bind_reg_read _ v); &(x, #b true, nil)). 
  (* register write *)
  refine ( let env := convert _ exprs in 
             let w := fst env in 
               x <- bind_expr _ w; 
           let e := ([neffect_reg_write _ v x])%list  in 
             &( unit, #b true, e)
         ). 
  (* register file read *)
  refine ( let env := convert _ exprs in 
             let adr := fst env in 
               adr <- bind_expr _ adr; 
           x <- bind_regfile_read _ _ v adr; 
           &( x, #b true, nil)
         ). 
  (* register file write *)
  refine ( let env := convert _ exprs in 
             match env with 
               | (adr, (w, _)) => 
                   adr <- bind_expr _ adr; 
                   w <- bind_expr _ w;
                   let e :=  ([neffect_regfile_write _ _ v  adr w])%list in                      
                     &( unit, #b true, e)                      
             end
         ). 
    (* or else *)  
  Defined. 
    Definition compile t a :=   
      (unit <- (bind_expr _ (# Ctt))%expr; compile_inner unit t a). 

  
  Inductive effect  : sync -> Type :=
  | effect_reg_write : forall t,  R t -> R Bool -> effect (Treg t)
  | effect_regfile_write : forall n t,  R t -> R (Tlift (Tfin n)) -> R Bool -> 
                                                effect (Tregfile n t). 
  
  Definition effects := Tuple.of_list (option ∘ effect) Phi. 
  
  Definition init_effects : effects := Tuple.init sync (option ∘ effect) (fun t : sync => None) Phi. 

  Definition block t := telescope (R t * expr R Bool *  effects). 
    
  Notation "e :-- t1 ; t2 " := (compose t1 (fun e => t2)) (right associativity, at level 80, e1 at next level).
  Arguments Tuple.set {T F l t} _ _ _.  

  Definition nblock_to_block {t} (B : nblock t) : block t. 
  unfold block, nblock in *. 
  
  Definition inversion_effect_Treg t (e : effect (Treg t)) : (R t * R Bool) :=
    match e with 
      | effect_reg_write _ x y => (x,y)
    end. 

  Definition inversion_effect_Tregfile t n (e: effect (Tregfile n t)): 
    (R t * R (Tlift (Tfin n)) *R Bool) :=
    match e with 
      | effect_regfile_write _ _ x y z => (x,y,z)
    end. 

  Definition merge s (a b : effect s) : telescope (effect s). 
  refine (match s as s'  return effect s' -> effect s' -> telescope (effect s') with 
              | Treg t => fun a b => 
                           let (va,ga) := inversion_effect_Treg t a in 
                           let (vb,gb) := inversion_effect_Treg t b in 
                             (
                               we <- bind_expr  _ (!ga || !gb)%expr ;
                               w <- bind_expr  _ (Emux _ _ (!ga) (!va) (!vb) )%expr ;
                               & (effect_reg_write  _ w we))
              | Tregfile n t => fun a b => 
                           match inversion_effect_Tregfile t n a with 
                             | (va,adra,ga) =>
                                 match inversion_effect_Tregfile t n b with 
                                   | (vb,adrb,gb) =>
                                       (
                                         we <- bind_expr  _ (!ga || !gb)%expr; 
                                         wadr <- bind_expr _ (Emux _ _ (!ga) (!adra) (!adrb))%expr; 
                                         wdata <- bind_expr _ (Emux _ _ (!ga) (!va) (!vb))%expr; 
                                         &  (effect_regfile_write _ _ wdata wadr we))
                                 end
                           end
          end a b). 
  Defined. 

    (** We give the priority to the old write here  *)
  Definition update t (v : var Phi t) (e : effect t)  (acc: effects) : telescope effects. 
  refine ( match Tuple.get _  _ v acc with 
               | Some old => 
                   e :-- merge t old e ; & (Tuple.set v (Some e) acc)
               | None => 
                   & (Tuple.set v (Some e) acc)
           end). 
  Defined. 
                                                                       

  Fixpoint compile_neffect (G : expr R Bool) (E : neffect) (B : effects) : telescope effects :=
    match E with               
      | neffect_guard guard L => 
                    let compile_neffects := fix compile_neffects G l U :=
                        match l with 
                          | nil =>  & U
                          | cons t q => 
                              compose (compile_neffect G t U)
                                      (compile_neffects G q)
                        end in 
                      compile_neffects (G && guard)%expr L B
      | neffect_reg_write t v val => 
          G <- bind_expr _  G;
          update (Treg t) v (effect_reg_write t val G) B
      | neffect_regfile_write n t v adr val => 
          G <- bind_expr _  G;
          update (Tregfile n t) v (effect_regfile_write n t val adr G) B
    end.  

    
  Fixpoint compile_neffects (G : expr R Bool)(l : list neffect)  (T : effects) :
    telescope effects :=
    match l with 
      | nil =>  & T
      | cons t q => 
          compose (compile_neffect G  t T)
                  (compile_neffects G q)
    end. 

  (* guard was replaced by true  *)
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
              | bind_reg_read v => (Tuple.get _ _ v st)
              | bind_regfile_read n v adr => 
                  let rf := Tuple.get Phi (Tregfile n t) v st in
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
          Core.Diff.add Phi Delta (Treg t) v w 
      | neffect_regfile_write  n t v adr w  =>  
          let rf := Tuple.get Phi (Tregfile n t) v st in                          
            let rf := Regfile.set rf adr  w in 
              Core.Diff.add Phi Delta (Tregfile n t) v rf            
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
    refine (Tuple.map3 _ Phi e st Delta). 

    Definition eval_effect (a : sync) :   
      (option ∘ effect eval_type) a ->
      eval_sync a -> (option ∘ eval_sync) a -> (option ∘ eval_sync) a. 
    
    refine (fun  eff => 
              match eff with 
                  | Some eff =>  
                      match eff in effect _ s return eval_sync s -> (option ∘ eval_sync) s -> (option ∘ eval_sync) s  with 
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
    (* Definition eval_effect (a : sync) :    *)
    (*   (option ∘ effect eval_type) a -> *)
    (*   var Phi a -> updates -> updates.  *)
    
    (* refine (fun  eff =>  *)
    (*           match eff with  *)
    (*               | Some eff =>   *)
    (*                   match eff in effect _ s return var Phi s -> updates -> updates with    *)
    (*                     |  effect_reg_write t val we =>   *)
    (*                          fun v Delta => *)
    (*                            if we then Tuple.set v (Some val) Delta else Delta *)
    (*                     |  effect_regfile_write n t val adr we =>  *)
    (*                          fun v Delta =>  *)
    (*                            if we then  *)
    (*                              let rf := Tuple.get Phi (Tregfile n t) v st in                     *)
    (*                              let rf := Regfile.set rf adr val in  *)
    (*                                  Tuple.set v (Some rf) Delta             *)
    (*                            else *)
    (*                              Delta *)
    (*                   end *)
    (*               | None => fun v Delta => Delta *)
    (*           end).  *)
    (* Defined.  *)

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


  (* Notation "x <-- e1 ; e2" := (telescope_bind  _ _ _ e1 (fun x => e2)) (right associativity, at level 80, e1 at next level).   *)
  (* Notation " & e " := (telescope_end  _ _ e) (at level 71).  *)
  (* Notation "[< r , g , e >] :- t1 ; t2 " := (compose  _ t1 (fun r g e => t2)) (right associativity, at level 80, t1 at next level).  *)
  
  Section correctness. 
  
    
    Notation C := (compile_inner eval_type tt). 
    Lemma eval_andb_true x y : (eval_expr Bool (andb eval_type x y)) = (eval_expr Bool x && eval_expr Bool y)%bool.
    Proof. 
      Require Import Equality Bool. 
      
      dependent destruction x; dependent destruction y; simpl;
      repeat match goal with 
                 c : constant0 B |- _ => destruct c
               | x : eval_type Bool |- _ => destruct x
               | _ => idtac
             end; rewrite ?andb_true_r, ?andb_true_l, ?andb_false_l , ?andb_false_r ; reflexivity.  
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
    Theorem CPS_compile_correct t (a : action Phi eval_type t)  Delta:
      eval_nblock st _ (C t a ) Delta =  (Core.Sem.eval_action a st Delta).
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
        case_eq (eval_expr Bool gA); intros H.  simpl.
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
        + simpl.
              
          set (x := DList.to_tuple eval_expr exprs). 
          replace (x) with (fst x, snd x) by (destruct x; reflexivity).

          Lemma convert_commute  l (dl : DList.T (expr eval_type) l): map  _ _ _ (eval_expr) l (convert _ l dl) = DList.to_tuple (eval_expr) dl. 
          Proof. 
            induction dl. simpl. reflexivity. 
            simpl. f_equal. apply IHdl. 
          Qed. 
          simpl. 
    
          replace (eval_expr t (fst (convert eval_type [t] exprs))) with (fst x). reflexivity. 
          subst x. rewrite <- convert_commute. simpl. reflexivity.  

        + simpl. 
          rewrite <- convert_commute. simpl. reflexivity.
        + simpl. 
          rewrite <- convert_commute. simpl. 
          case_eq (convert eval_type ([Tlift (Tfin n); t])%list exprs). 
          intros adr [value tt] H.  simpl. simpl in tt.           
          reflexivity. 

      - intros. simpl.   unfold Sem.Dyn.OrElse. 
        rewrite <- IHa1, <- IHa2 . clear IHa1 IHa2. 
        generalize (C t a1); intros T; generalize (C t a2); intros T'. 
        induction T as [[[rA gA] eA] |]; simpl.
        induction T' as [[[rA' gA'] eA'] |]. simpl compose.
        t. simpl. rewrite check0. simpl.  t. reflexivity. 
        simpl. rewrite check0. simpl. t; reflexivity.  
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
  
  Lemma prefold_idempotent : forall T B (F : T -> Type) (l : list T)
                               (up : forall a, F a -> var l a -> B -> B),
                               (forall a (x : F a) v acc, up a x v acc = acc)
                               -> forall s f ol acc, Tuple.prefold l up s f ol acc = acc.
  induction s; t.
  Qed.
    
  Lemma prefold_2  : forall T B (F : T -> Type ) (l : list T)
                       (up : forall a, F a -> var l a -> B -> B), 
                       forall s f (ol : Tuple.of_list F s), 
                         (forall a  v acc, up a (Tuple.get _ _ v ol) (f _ v) acc = acc) ->
                         forall acc, Tuple.prefold l up s f ol acc = acc. 
  Proof. 
  induction s; t. destruct ol as [hd tl]. rewrite IHs.  
  specialize (H a var_0). simpl in H. 
  apply H.   
  intros. specialize (H a0 (var_S v)). simpl in H. apply H. 
  Qed. 
 
  
  Lemma eval_effect_init Phi st Delta : eval_effects Phi st (init_effects Phi eval_type) Delta = Delta. 
  Proof.
    unfold eval_effects. 
    induction Phi. simpl. reflexivity. 
    simpl. destruct st. destruct Delta. f_equal. apply IHPhi. 
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
    (forall (guard : expr R Bool) ,
       P (neffect_guard Phi  R guard [])) ->
    (forall (guard : expr R Bool) a l ,
       P a -> P (neffect_guard Phi  R guard l) ->
       P (neffect_guard Phi  R guard (a :: l))) ->
    (forall (t : type) (v : var Phi (Treg t)) (r : R t),
       P (neffect_reg_write  Phi R t v r)) ->
    (forall (n : nat) (t : type) (v : var Phi (Tregfile n t))
       (r : R (Tlift (Tfin n))) (r0 : R t),
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
                               compile_neffect Phi eval_type g1 (neffect_guard Phi eval_type g2 l) e = (compile_neffects Phi eval_type (g1 && g2)%expr l e).
  Proof.                                                                                        
    induction l; reflexivity.
  Qed. 
  
  Lemma eval_neffect_cons Phi st guard a l Delta: 
    eval_neffect Phi st (neffect_guard Phi eval_type guard (a :: l)) Delta = 
                 (if eval_expr Bool guard
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
                                         = if eval_expr Bool guard then eval_neffects Phi st l Delta else Delta.
  Proof. 
    reflexivity. 
  Qed. 
    

  
  Notation "[[ x ]]" := (eval_expr Bool x). 
  Arguments Tuple.set {T F l t} _ _ _.
  Arguments Tuple.get {T F l t} _ _. 

  Notation Ev Phi st  := (eval_telescope Phi st (eval_effects Phi st)).  
  
  Ltac v := match goal with 
                |- context [match ?X with  | ( _ , _  )  => _ end ] => destruct X 
            end. 

              Ltac d := match goal with 
                          | H : context [match ?X with | _ => _ end] |- _ => dependent destruction X
                          |  |- context [match ?X with | _ => _ end] => case_eq  X; intros; subst; simpl
                                                                                              
              end. 

  Lemma rew_1 Phi st Delta t (v : var Phi t ) x e : 
    eval_effects Phi st (Tuple.set v (Some x) e) Delta =
                 Tuple.set v (eval_effect t (Some x) (Tuple.get v st) (Tuple.get v Delta))  (eval_effects Phi st e Delta).  
  Proof. 
    induction Phi; [dependent destruction v|]. 
    dependent destruction v. 
    simpl; repeat v; destruct x; simpl; d; f_equal.
    simpl. repeat v; destruct x; simpl; rewrite IHPhi; clear IHPhi; 
           simpl; repeat d; simpl in *; auto. 
  Qed. 

  Lemma inversion_1 Phi st : forall t (v : var Phi (Treg t)) e Delta x x', 
                             inversion_effect_Treg eval_type t x = (x', true) ->
                             Tuple.get v e = Some x ->
                             exists y, Tuple.get v (eval_effects Phi st e Delta) = Some y.
  Proof. 
    induction Phi; [dependent destruction v|]. 
    dependent destruction v; simpl; intros. 
    repeat v; dependent destruction x; simpl in *; inversion H; subst; clear H; simpl.
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
        intros H. specialize (H Delta e (g && guard)%expr). revert H. 
        induction (C (g && guard)%expr a e); intros. 
         {simpl. rewrite IHa0. rewrite folder. simpl. simpl in H. rewrite H. 
         destruct ([[g]]); destruct ([[guard]]); simpl; try reflexivity. }
         {
         simpl. rewrite H. reflexivity. 
         simpl. simpl in *. rewrite H0. reflexivity.
         apply IHa0.          
         }
      - intros. simpl.
        unfold update. 
        case_eq (Tuple.get  v e); intros; simpl. 
        +               
        (* case: there was a previous effect on this register *)
        case_eq (inversion_effect_Treg eval_type t e0); intros; simpl.       
          
        
        rewrite rew_1. 
        case_eq (e2); intros; simpl. 
          * destruct ([[g]]). 
            subst. 
            {
              Lemma hint_1 Phi : forall st t (v : var Phi (Treg t)) r Delta e  e0, 
                                 Tuple.get v e = Some e0 -> 
                                 forall e1, inversion_effect_Treg eval_type t e0 = (e1, true) -> 
                                       Tuple.set v
                                            match Tuple.get v Delta with
                                                | Some _ => Tuple.get v Delta
                                                | None => Some e1
              end (eval_effects Phi st e Delta) =
                                          Diff.add Phi (eval_effects Phi st e Delta) (Treg t) v r. 
              Proof. 
                
                induction Phi; [dependent destruction v|].
                simpl. intros; repeat v. 
                 dependent destruction v; simpl; intros. 
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
              repeat d; clear IHPhi; dependent destruction e0;subst; f_equal; auto. 
              simpl in H0. inversion H0. auto.
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
              repeat d; repeat f_equal. 
              
              setoid_rewrite IHPhi. clear IHPhi. unfold Diff.add. simpl. repeat d; f_equal. auto. 
          }

      - intros. simpl.         unfold update. 
        case_eq (Tuple.get v e); intros; simpl. 
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
            unfold Diff.add; repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi;  auto. 
            unfold Diff.add; repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
          }
          subst. 
          {
            induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst. 
            unfold Diff.add; repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi;  auto. 
          }

          *destruct [[g]]. subst. 
          unfold Diff.add. 
          {
              induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst. 
            unfold Diff.add; repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi;  auto. 
            repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.          
          }
          {
            induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst. unfold Diff.add.
            repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi; auto. }
          
          
        + rewrite rew_1. simpl.
          unfold Diff.add. 
          {
            induction Phi; [dependent destruction v|].
            simpl; repeat v. 
            dependent destruction v; simpl in *; subst. unfold Diff.add.
            repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto.
            rewrite IHPhi; clear IHPhi; auto. 
            repeat d; repeat f_equal; dependent destruction e0; simpl in H'; inversion H'; subst;  try congruence; try simpl in *; try auto. 

          }
    Qed. 
    Print Assumptions compile_effect_correct. 

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
  Print Assumptions nblock_compile_correct. 
  
(*
  
  Definition compile  t (a : action Phi R t) : telescope (R t * expr R Bool * list effect).  
  refine (
      let f := fix compile t (a : action Phi R t) : telescope (R t * expr R Bool * list effect):= 
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
                & (varunit, !x, nil)%expr
            | Primitive args res p exprs => _
            (* | Try A =>  *)
            (*     [< rA, gA, eA >] :- compile _ A; *)
            (*     let e := effect_guard gA eA in *)
            (*       & (varunit, #b true, [e])%list *)
            (*     (* & (varunit, gA, eA) *) *)
            | OrElse t A A' => 
                [< rA, gA, eA >] :- compile _ A;
                [< rA', gA', eA' >] :- compile _ A';
                let e := effect_guard gA eA in 
                let e' := effect_guard ((~ gA) &&  gA')%expr eA' in 
                  r <- (bind_expr _ (Emux _ _ gA (!rA) (!rA'))%expr); 
                  & ( r , (gA || gA')%expr , [e;e'])%list
          end in f t a).
  (* primitive *)
  revert exprs. 
  refine (match p with
            | register_read t v => _
            | register_write t v => _
            | regfile_read n t v p => _
            | regfile_write n t v p => _
          end); clear p; intros exprs. 
  (* register read *)
  refine (x <- (bind_reg_read _ v); &(x, #b true, nil)). 
  (* register write *)
  refine ( let env := convert _ exprs in 
             let w := fst env in 
               x <- bind_expr _ w; 
           let e := ([effect_reg_write _ v x])%list  in 
             &( varunit, #b true, e)
         ). 
  (* register file read *)
  refine ( let env := convert _ exprs in 
             let adr := fst env in 
               adr <- bind_expr _ adr; 
           x <- bind_regfile_read _ _ v _ adr; 
           &( x, #b true, nil)
         ). 
  (* register file write *)
  refine ( let env := convert _ exprs in 
             match env with 
               | (adr, (w, _)) => 
                   adr <- bind_expr _ adr; 
                   w <- bind_expr _ w;
                   let e :=  ([effect_regfile_write _ _ v _ adr w])%list in                      
                     &( varunit, #b true, e)                      
             end
         ). 
    (* or else *)
  
  Defined. 
  
  Definition wrap t (T : preblock t) : block. 
  Proof. 
    eapply compose. apply T. 
    intros _ g e. 
    refine (            let e := effect_guard g e in 
                          & (cons e nil )). 
  Defined. 
  End defs. 
  
  (** * Semantics *)
  Section sem. 
    Variable st : eval_state Phi. 
    Definition eval_bind t (b : bind eval_type t) : (eval_type t).
    refine (match b with
              | bind_expr x =>  (eval_expr _ x)
              | bind_reg_read v => (Tuple.get _ _ v st)
              | bind_regfile_read n v p adr => 
                  let rf := Tuple.get Phi (Tregfile n t) v st in
                    Regfile.get rf (Word.unsigned adr)                
            end
           ). 
    Defined. 
    
    Definition up {A} (x : option A) y := match x with None => y | Some y => y end.  
                                                                
    Fixpoint eval_effect (e :effect eval_type) (Delta : updates) : updates :=    
      match e with 
        | effect_guard g l' => 
            let fix eval_effects l Delta := 
                match l with 
                  | nil => Delta
                  | cons e q =>  
                      let Delta := eval_effect e Delta in 
                        eval_effects q Delta
                end in     
              match eval_expr _ g with 
                | true =>  (* match eval_effects l' Delta with *)
                    (*     | Some Delta => Some Delta *)
                    (*     | None => Some Delta *)
                        (* end                         *)
                    eval_effects l' Delta
                | false => Delta
            end
      | effect_reg_write t v w =>                                               
          Core.Diff.add Phi Delta (Treg t) v w 
      | effect_regfile_write  n t v p adr w  =>  
          let rf := Tuple.get Phi (Tregfile n t) v st in                          
            let rf := Regfile.set rf (Word.unsigned adr) w in 
              Core.Diff.add Phi Delta (Tregfile n t) v rf            
    end. 
  
    Fixpoint eval_effects ( l : list (effect eval_type)) Delta : updates :=
      match l with 
        | nil =>  Delta
        | cons e q => (* do Delta <- eval_effect e Delta;  *)
            let Delta :=  (eval_effect e Delta) in 
            eval_effects q Delta
      end. 
  
    Lemma fold_eval_effects :
      (fix eval_effects l Delta := 
       match l with 
                | nil =>  Delta
                | cons e q => 
                    let Delta := (eval_effect e Delta) in 
                      (* do Delta <- eval_effect e Delta;  *)
                      eval_effects q Delta
       end)= eval_effects .
    Proof. 
      unfold eval_effects. reflexivity.
    Qed. 
    
    (* Lemma eval_effects_cons  t q Delta :  *)
    (*   eval_effects (t :: q) Delta = do Delta' <- eval_effect  t Delta; eval_effects q Delta'.  *)
    (* Proof. *)
    (*   reflexivity.  *)
    (* Qed.  *)
    
    (* Lemma eval_effect_guard (gA : expr eval_type Bool) eA Delta:  *)
    (*   eval_expr  _ gA = true -> *)
    (*   eval_effect  (effect_guard eval_type gA eA) Delta = eval_effects eA Delta.  *)
    (* Proof.  *)
    (*   intros. simpl. rewrite (fold_eval_effects).  *)
    (*   rewrite H. reflexivity.  *)
    (* Qed.  *)

    Fixpoint eval_preblock t  (T : preblock  eval_type t) :
      updates -> option (eval_type t * updates) := 
      match T with
        | telescope_bind arg bind cont => 
            fun Delta => 
              let res := eval_bind _ bind in
              eval_preblock _ (cont res) Delta
        | telescope_end (p, g, e) => fun Delta =>
                                      let g := eval_expr _ g  in             
                                      if g then                                         
                                        Some (p, eval_effects e Delta)
                                      else None
    end. 
  
  
    Fixpoint eval_block (a : block eval_type) {struct a}: updates ->  updates :=
      match a with
        | telescope_bind arg bind cont => 
            fun Delta => 
              let res  := eval_bind _ bind in 
                eval_block (cont res) Delta
        | telescope_end effects => eval_effects effects
      end. 
    
  End sem. 


  Notation "x <-- e1 ; e2" := (telescope_bind  _ _ _ e1 (fun x => e2)) (right associativity, at level 80, e1 at next level).  
  Notation " & e " := (telescope_end  _ _ e) (at level 71). 
  Notation "[< r , g , e >] :- t1 ; t2 " := (compose  _ t1 (fun r g e => t2)) (right associativity, at level 80, t1 at next level). 
  
  Section correctness. 
  
    
    
    Notation C := (compile eval_type tt). 
    Lemma eval_andb_true x y : (eval_expr Bool (andb eval_type x y)) = (eval_expr Bool x && eval_expr Bool y)%bool.
    Proof.
      Require Import Equality. 
      dependent destruction x. simpl. 
    Admitted.  

    Lemma eval_effects_append  st e f (Delta : updates) : 
      eval_effects st (e ++ f) Delta = 
                   eval_effects st f (eval_effects st e Delta).              
    Proof. 
      revert Delta. 
      induction e. 
      + reflexivity. 
      + intros Delta.
        
        simpl. rewrite IHe. reflexivity.  

    Qed. 

    Variable st : eval_state Phi. 

    Notation "B / Delta " := (eval_preblock st _ B Delta). 
    Theorem CPS_compile_correct t (a : action Phi eval_type t)  Delta:
      eval_preblock st _ (C t a ) Delta =  (Core.Sem.eval_action a st Delta).
    Proof. 
      revert Delta. 
      induction a. 
      - intros.  reflexivity. 
      - intros Delta. simpl. unfold  Sem.Dyn.Bind. rewrite <- IHa.
        transitivity (do ed <- (C t a) / Delta ; 
                      let (e,d) := ed in 
                      eval_preblock st u (C u (f e)) d
                   ); 
        [|destruct  ((C t a) / Delta) as [[ e d ]| ]; simpl; easy]. 
        clear IHa H.
        generalize (C t a) as T. intros T. clear a.
        
        induction T. destruct a as [[rA gA] eA]. 
        simpl in *. 
        case_eq (eval_expr Bool gA); intros H.  simpl.
        induction (C u (f rA)). destruct a as [[rB gB] eB]. simpl. 
        * rewrite eval_effects_append. rewrite eval_andb_true. rewrite H. simpl. reflexivity. 
        * simpl. rewrite H0. reflexivity.         

        * induction (C u (f rA)). destruct a as [[rB gB] eB]. simpl. 
          rewrite eval_andb_true. rewrite H. reflexivity.  
          simpl. rewrite H0. reflexivity. 
        * simpl. rewrite H. reflexivity.

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
        + simpl.
              
          set (x := DList.to_tuple eval_expr exprs). 
          replace (x) with (fst x, snd x) by (destruct x; reflexivity).

          Lemma convert_commute  l (dl : DList.T (expr eval_type) l): map  _ _ _ (eval_expr) l (convert _ l dl) = DList.to_tuple (eval_expr) dl. 
          Proof. 
            induction dl. simpl. reflexivity. 
            simpl. f_equal. apply IHdl. 
          Qed. 
          simpl. 
    
          replace (eval_expr t (fst (convert eval_type [t] exprs))) with (fst x). reflexivity. 
          subst x. rewrite <- convert_commute. simpl. reflexivity.  

        + simpl. 
          rewrite <- convert_commute. simpl. reflexivity.
        + simpl. 
          rewrite <- convert_commute. simpl. 
          case_eq (convert eval_type ([Tlift (W p); t])%list exprs). 
          intros adr [value tt] H.  simpl. simpl in tt.           
          reflexivity. 

      - intros. simpl.   unfold Sem.Dyn.OrElse. 
        rewrite <- IHa1, <- IHa2 . clear IHa1 IHa2. 
        generalize (C t a1); intros T; generalize (C t a2); intros T'. 
        induction T as [[[rA gA] eA] |]; simpl.
        induction T' as [[[rA' gA'] eA'] |]. simpl compose.
        t. simpl. rewrite check0. simpl.  t. reflexivity. 
        simpl. rewrite check0. simpl. t; reflexivity.  
        simpl. rewrite H. reflexivity. 
        simpl. rewrite H. reflexivity.

    Qed.
End correctness. 
End t. 
Arguments telescope_bind {Phi R A arg}  _ _.  
Notation "'DO' X <- E ; F" := (telescope_bind E (fun X => F)).  
Notation "'RETURN' X" := (telescope_end _ _ _ X). 
Arguments bind_expr  {Phi R t} _%expr. 
Notation "[: v ]" := (bind_reg_read _ _ _ v).   
(* Section test.  *)
(*   Require Import MOD.  *)
(*   Definition Z (t : type) := unit.  *)
(*   Eval compute in compile _ Z _ _  (iterate 5 Z) .  *)

(*   Eval compute in compile _ Z _ _ (done 5 Z).  *)

(* End test.  *)

(* Section test2.  *)
(*   Require Import Isa.  *)
(*   Eval compute in compile _ _ 0 _ (loadi_rule 5 (fun _ => nat)).  *)

(*   Eval compute in compile _ _ 0 _ (store_rule 5 (fun _ => nat)).  *)

(* End test2.  *)

*)
End correctness2. 


