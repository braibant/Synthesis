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
  
  Variable varunit : R Unit. 
  
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
  Definition compile  t (a : action Phi R t) : telescope (R t * expr R Bool * list neffect).  
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
                & (varunit, !x, nil)%expr
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
             &( varunit, #b true, e)
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
                     &( varunit, #b true, e)                      
             end
         ). 
    (* or else *)
  
  Defined. 
  
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
  
  Definition inversion_effect_Treg : forall t, effect (Treg t) -> (R t * R Bool). 
  Proof. 
    intros. inversion X. subst. auto. 
  Defined. 

  Definition inversion_effect_Tregfile : forall t n, effect (Tregfile n t) -> 
                                                (R t * R (Tlift (Tfin n)) *R Bool). 
  Proof. 
    intros; inversion X. subst. auto. 
  Defined. 

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
    
    

    Definition eval_effects (e : effects eval_type) (Delta : updates) : updates.  
    unfold effects in e. 
    
    refine (Tuple.map3 _ Phi e st  Delta).
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
  
    
    Notation C := (compile eval_type tt). 
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
        transitivity (do ed <- (C t a) / Delta ; 
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
  Section correctness2. 
    Notation Cs  := (compile_neffects  _ ). 
    Notation C  := (compile_neffect  _). 
    Notation "x <- e1 ; e2" := (@telescope_bind _ _ _ e1 (fun x => e2)) (right associativity, at level 80, e1 at next level).  
    Notation " & e " := (@telescope_end _ _  e) (at level 71). 

    Notation "e :- t1 ; t2 " := (@compose  _ _ _ t1 (fun e => t2)) (right associativity, at level 80, t1 at next level).

    Variable st : eval_state Phi. 

    Lemma eval_effect_init Delta :eval_effects st (init_effects eval_type) Delta = Delta. 
    Proof. Admitted. 
    

        Lemma foo {R A B C} (T: telescope R A) (f : A -> telescope R B)  (g : B -> telescope R C) :
          (X :- (Y :- T; f Y); (g X) )= (Y :- T; X :- f Y; g X).
        Proof.
          induction T. reflexivity. simpl.
          f_equal.
          Require Import  FunctionalExtensionality.
          apply functional_extensionality.
          apply H.
        Qed.
        
        
        
        
        Lemma my_ind (R : type -> Type) (P : neffect  R -> Prop) :
          (forall (guard : expr R Bool) ,
             P (neffect_guard R guard [])) ->
          (forall (guard : expr R Bool) a l ,
             P a -> P (neffect_guard  R guard l) ->
             P (neffect_guard  R guard (a :: l))) ->
          (forall (t : type) (v : var Phi (Treg t)) (r : R t),
             P (neffect_reg_write R t v r)) ->
          (forall (n : nat) (t : type) (v : var Phi (Tregfile n t))
             (r : R (Tlift (Tfin n))) (r0 : R t),
             P (neffect_regfile_write  R n t v r r0)) ->
          forall n : neffect  R, P n. 
    Admitted. 
    Lemma correspondance l e : forall g1 g2, 
                                 compile_neffect eval_type g1 (neffect_guard  eval_type g2 l) e =
                                                 (compile_neffects eval_type (g1 && g2)%expr l e).                  
    induction l. simpl. reflexivity. 
    simpl. 
    intros. reflexivity. 
    Qed. 
    
    Lemma eval_neffect_cons  guard a l Delta: 
      eval_neffect st (neffect_guard  eval_type guard (a :: l)) Delta = 
                   (if eval_expr Bool guard
                    then eval_neffects st l (eval_neffect st a Delta)
                    else Delta). reflexivity. 
    Qed.

    Fixpoint eval_telescope {A B} (F : A -> B) (T : telescope eval_type A) :=
      match T with 
        | telescope_end X => F X
        | telescope_bind arg bind cont =>
            let res := eval_bind st arg bind in 
              eval_telescope F (cont res)
      end. 

    Lemma folder guard l Delta: eval_neffect st (neffect_guard eval_type guard l) Delta 
                                         = if eval_expr Bool guard then eval_neffects st l Delta else Delta.
    Proof. 
      reflexivity. 
    Qed. 
    

    Notation Ev := (eval_telescope (eval_effects st)). 
    Notation "[[ x ]]" := (eval_expr Bool x). 
    
    Lemma compile_effect_correct a  : forall Delta e g , eval_telescope (eval_effects st) (C g a e) Delta 
                               =  if [[g]] then eval_neffect st a (Ev (&e) Delta) else (Ev (&e)Delta). 
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
        case_eq (Tuple.get Phi (Treg t) v e); intros; simpl. 
        +               
        (* case: there was a previous effect on this register *)
        case_eq (inversion_effect_Treg eval_type t e0); intros; simpl.         
        Arguments Tuple.set {T F l t} _ _ _.
        Arguments Tuple.get {T F l t} _ _. 
        Lemma k t (v : var Phi (Treg t)) x e Delta : 
          let E := eval_effects st e Delta in 
          eval_effects st (Tuple.set v x e) Delta = 
                  Tuple.set v (eval_effect _ x (Tuple.get v st) (Tuple.get v Delta)) E.
        Proof. 

        Lemma tuple_map3_upd_1 {T F F' F''} (C : forall a : T, F a -> F' a -> F'' a -> F'' a) 
                               e T1 T2 T3 (t : T) (v : var e t) x: 
          Tuple.map3 C e (Tuple.set v x T1) T2 T3 = 
               Tuple.set v (C t x (Tuple.get v T2) (Tuple.get v T3) ) (Tuple.map3 C e T1 T2 T3). 
        Proof. 
        Admitted.
        simpl. unfold eval_effects. rewrite tuple_map3_upd_1. f_equal. 
        Qed. 
        rewrite k. simpl.

        unfold Diff.add.
        
        Notation tuple_update v r T := (match Tuple.get v T with 
                                            | Some _ => T
                                            | None => Tuple.set v r T end). 
        
        match goal with 
            |- Tuple.set ?v  ?l = ?r =>
              transitivity (tuple_update v x l)
        end.
        

        Lemma set_get  t (v : var Phi (Treg t)) (T : updates) x :  
          Tuple.set v (match Tuple.get v T with Some _ => Tuple.get v T | None => x end) T =
               match Tuple.get v T with 
                   | Some _ => T 
                   | None => Tuple.set v x T
         end. 
    Admitted. 
     rewrite (set_get t v (eval_effects st e Delta)). 
    Qed. 
        
        simpl. 
        rewrite tuple_map3_upd_1.
        match goal with 
          | |- context [Tuple.map3 ?F ?l ?T1 ?T2 ?T3] => 
              change (Tuple.map3 F l T1 T2 T3) with (eval_effects T2 T1 T3)	      
          end.
          
          unfold Diff.add. 
          destruct ([[g]]). 
          case_eq (Tuple.get v Delta). intros.
          Lemma prop_effect_1 e t (v : var Phi t) x Delta : Tuple.get v e = Some x -> 
                                            exists y, Tuple.get v  (eval_effects st e Delta) = Some y. 
          Proof. 
          Admitted. 
          destruct (prop_effect_1 _ _ _ _  Delta H).
          Set Printing All. rewrite H2. 
        destruct ([[g]]). simpl. reflexivity. 
        simpl. 
        
        unfold eval_effects. simpl. 
        rewrite tuple_map3_upd_1. 
        match goal with 
            |- context [Tuple.map3 ?f _ _ _ _] => set (F := f)
        end. 
        generalize (Tuple.map3 F Phi e st Delta). intros o. 
        case_eq b. intros. 
        unfold Diff.add. destruct (Tuple.get v Delta). 
        unfold eval_effects. rewrite tuple_map3_upd_1. 
        Lemma eval_effect_upd : 
          eval_effects st (Tuple.set v ) Delta
        
          unfold eval_effects. 
          simpl. 
        admit. 

      - admit. 
    Qed. 

                                 
        
    Lemma zoby es : forall Delta e g, eval_telescope (eval_effects st) (Cs g es e) Delta 
                               =  if [[g]] then eval_neffects st es (Ev (&e) Delta) else Ev (&e) Delta. 
    Proof. 
      induction es. 
      intros; simpl.  destruct ([[g]]); reflexivity.  
      simpl. intros. 
      pose (H := zob a Delta e g).
      clearbody H. revert H. 
      induction (C g a e). 
      - simpl.       intros H. 
      rewrite IHes. simpl. rewrite H. destruct ([[g]]); reflexivity.
      - simpl. intros. apply H. simpl. auto. 

    Qed. 

    Theorem nblock_compile_correct t (nb : nblock eval_type t)  Delta:
      eval_block st t (nblock_to_block eval_type nb) Delta =  eval_nblock st _ nb Delta. 
    Proof. 
      unfold nblock in nb. 
      induction nb as [ [ [rA gA] eA]|]. 
      2: simpl; rewrite <- H; reflexivity. 
      
      {
        unfold nblock_to_block. unfold compose_block. simpl.
        pose (H := zoby eA Delta (init_effects eval_type) gA). 
        clearbody H. 
        case_eq ([[gA]]).
        {
          intros. rewrite H0 in H. simpl in H. 
          rewrite eval_effect_init in H. 
          rewrite <- H. clear H.  
          induction (Cs gA eA (init_effects eval_type)). simpl. rewrite H0. reflexivity. 
          simpl. rewrite <- H. reflexivity. 
        }
        {
          intros.
          induction (Cs gA eA (init_effects eval_type)). simpl. rewrite H0. reflexivity. 
          simpl. apply H1. auto.          
        }
      }

    Qed. 
    Print Assumptions nblock_compile_correct. 
  
  

  End correctness2. 
  End t. 
Notation "e :- t1 ; t2 " := (@compose _ _ _ _ t1 (fun e => t2)) (right associativity, at level 80, t1 at next level).

Notation Psi := (init_effects _ _). 

Theorem nblock_compile_correct Phi (st : eval_state Phi) t (nb : nblock Phi eval_type t)  Delta:
  eval_block Phi st _  (nblock_to_block Phi eval_type nb) Delta =  eval_nblock Phi st _ nb Delta. 
unfold nblock in nb. 
induction nb as [[[rA gA] eA]|]. unfold nblock_to_block. unfold compose_block. simpl.
revert Delta t rA gA st . induction eA. simpl.
intros. case_eq (eval_expr Bool gA); try reflexivity. intros. 
f_equal. f_equal. 
clear. 
Lemma eval_effect_init Phi st Delta :   eval_effect Phi st (init_effects Phi eval_type) Delta = Delta. 
Proof. 
  induction Phi. reflexivity.
destruct st as [hd tl].
destruct Delta as [delta Delta].
simpl.   
f_equal.  apply IHPhi.  
Qed. 
now (apply eval_effect_init). 
intros.  simpl eval_neffects. rewrite <- IHeA.  clear IHeA.
simpl compile_neffects.

Lemma foo {Phi R A B C} (T: telescope Phi R A) (f : A -> telescope Phi R B)  (g : B -> telescope Phi R C) : 
  (X :- (Y :- T; f Y); (g X) )= (Y :- T; X :- f Y; g X). 
Proof. 
  induction T. reflexivity. simpl.
  f_equal. 
  Require Import  FunctionalExtensionality. 
  apply functional_extensionality. 
  apply H. 
Qed. 
rewrite foo.
Lemma my_ind (Phi : state) (R : type -> Type) (P : neffect Phi R -> Prop) :
  (forall (guard : expr R Bool) ,
        P (neffect_guard Phi R guard [])) ->
  (forall (guard : expr R Bool) a l ,
        P a -> P (neffect_guard Phi R guard l) ->
        P (neffect_guard Phi R guard (a :: l))) ->
  (forall (t : type) (v : var Phi (Treg t)) (r : R t),
     P (neffect_reg_write Phi R t v r)) ->
  (forall (n : nat) (t : type) (v : var Phi (Tregfile n t))
          (r : R (Tlift (Tfin n))) (r0 : R t),
     P (neffect_regfile_write Phi R n t v r r0)) ->
  forall n : neffect Phi R, P n. 
Admitted. 
Lemma correspondance Phi l : forall g1 g2, 
  compile_neffect Phi eval_type g1 (neffect_guard Phi eval_type g2 l) Psi =
  (compile_neffects Phi eval_type (g1 && g2)%expr l Psi).                  
induction l. simpl. reflexivity. 
simpl. 
intros. reflexivity. 
Qed. 
Lemma eval_neffect_cons Phi st guard a l Delta: 
  eval_neffect Phi st (neffect_guard Phi eval_type guard (a :: l)) Delta = 
 (if eval_expr Bool guard
  then eval_neffects Phi st l (eval_neffect Phi st a Delta)
else Delta). reflexivity. 
Qed.

Lemma update_init Phi t v x : update Phi eval_type t v x Psi = & (Tuple.set _ _ Phi t v (Some x) Psi). Admitted.

Definition lr Phi st  (e : effects Phi eval_type) (Delta: Tuple.of_list (comp option eval_sync) Phi) :=
  eval_effect Phi st e Delta = Delta. 
admit. 

{simpl. rewrite <- H. clear H. reflexivity. }

Inductive correct Phi  st t f  := 
  test : forall Delta t0 v g r, 
  eval_block Phi st t
     (X
      :- &
         Tuple.set sync (option ∘ effect eval_type) Phi 
           (Treg t0) v
           (Some (effect_reg_write eval_type t0 r g))
           Psi; f X) Delta =
   eval_block Phi st t (f Psi)
     (if g
      then
       match Tuple.get Phi (Treg t0) v Delta with
       | Some _ => Delta
       | None =>
           Tuple.set sync (option ∘ eval_sync) Phi (Treg t0) v (Some r) Delta
       end
      else Delta) -> correct Phi st t f.   

Lemma eval_block_cons  Phi st t a : forall Delta guard f (H : correct Phi st t f), 
  eval_block Phi st t (X :- C guard a Psi; f X) Delta = 
  eval_block Phi st t (f Psi) (if eval_expr _  guard then eval_neffect Phi st a Delta else Delta). 

induction a using my_ind. 
- intros. simpl. destruct (eval_expr Bool guard); destruct (eval_expr _ guard0); reflexivity. 
- intros. rewrite correspondance. 
intros. rewrite eval_neffect_cons. simpl.   
rewrite foo.
rewrite IHa. clear IHa. simpl. setoid_rewrite correspondance in IHa0.
simpl compose in IHa0. simpl eval_block in IHa0 at 1. rewrite IHa0. clear IHa0. 
case_eq (eval_expr Bool guard); intros; case_eq (eval_expr _ guard0); intros. 
simpl Datatypes.andb. cbv iota. f_equal. simpl. rewrite H. 
reflexivity. 
simpl. reflexivity. 
intros. unfold Datatypes.andb.
f_equal. simpl. rewrite H. reflexivity. 

intros. simpl.  reflexivity. 
- intros. simpl.
unfold Diff.add.
rewrite update_init.
simpl. 
Admitted. 
Admitted. rewrite eval_block_cons. 
simpl. reflexivity.  
simpl. rewrite <- H. clear H. reflexivity. 
Qed. 

Print Assumptions nblock_compile_correct. 


  
  Section defs2. 
  Variable R : type -> Type. 
  
  
  Arguments effect_guard guard%expr effects%list. 
  
  (** * Compilation *)
  (** This 'smart constructor' reduces the size of the guard, by using
  the fact that [true] is a neutral element for [&&] *)
  
  Definition andb (a b : expr R Bool): expr R Bool :=
    match a, b with 
      | Econstant Tbool x, o 
      | o, Econstant Tbool x => if x then o else (#b false)%expr
      | _, _ => (a && b)%expr
    end. 
  
  (**  The compilation function itself *)
  Variable varunit : R Unit. 
  
  Definition convert  l : DList.T (expr R) l -> Tuple.of_list (expr R) l := DList.to_tuple (fun t X => X). 

  Fixpoint map T F F' (G : forall t, F t -> F' t) (l : list T) : Tuple.of_list F l -> Tuple.of_list F' l:=
    match l with 
      | nil => fun x => x
      | cons t q => fun x => (G t (fst x), map T F F' G q (snd x))
    end. 

  Arguments map {T F F'} G l _. 
  (*  fst (DList.T_fold' eval_expr [t] exprs) =
   eval_expr t
     (fst
        (DList.T_fold' (fun (t0 : type) (X : expr eval_type t0) => X) [t] exprs))

*)
  
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

