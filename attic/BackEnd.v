Require Import Common. 
Require RTL Core. 
Import Core. 
Section t. 
  
  Variable Phi : state. 
  Notation updates := (Tuple.of_list (option ∘ Core.eval_sync) Phi). 
  
  Section defs. 
  Variable R : type -> Type. 

  (** Combinational bindings (expressions, register reads)  *)
  (* Inductive bind (t : type) : Type :=  *)
  (* | bind_expr :  expr R t ->  bind t *)
  (* | bind_reg_read : var Phi (Treg t) -> bind t *)
  (* | bind_regfile_read : forall n, var Phi (Tregfile n t) -> forall p, R (Tlift (W p)) -> bind t.  *)

  (* Inductive telescope (A : Type): Type := *)
  (* | telescope_end : A -> telescope A *)
  (* | telescope_bind : forall arg, bind arg -> (R arg -> telescope A) -> telescope A.  *)
  
  
  Inductive effect  : sync -> Type :=
  | effect_reg_write : forall t,  R t -> R Bool -> effect (Treg t)
  | effect_regfile_write : forall n t,  R t -> R (Tlift (Tfin n)) -> R Bool -> 
                                                effect (Tregfile n t). 
  
  Definition effects := Tuple.of_list (effect) Phi. 

  Definition block t := RTL.telescope Phi R (R t * expr R Bool *  effects). 
  
  (* Fixpoint compose {t B}  *)
  (*                  (tA : block t) *)
  (*                  (f : R t -> expr R Bool -> effects -> telescope B) : *)
  (*   telescope B := *)
  (*   match tA with *)
  (*     | telescope_end ((r,g),e) => f r g e *)
  (*     | telescope_bind arg b cont => telescope_bind _ arg b (fun x => compose (cont x) f)  *)
  (*   end.  *)
  
  Notation "x <- e1 ; e2" := (telescope_bind _ _ e1 (fun x => e2)) (right associativity, at level 80, e1 at next level).  
    
  Notation "[< r , g , e >] :- t1 ; t2 " := (compose t1 (fun r g e => t2)) (right associativity, at level 80, e1 at next level). 
  Notation " & e " := (telescope_end _ e) (at level 71). 
  Arguments Tuple.set {T F l t} _ _ _.  
  Definition compile {t} (B : RTL.block Phi R) : block t. 
  

  Definition compile_effect t (E : RTL.effect Phi R) (B : block t) : block t. 
  refine (let compile := fix compile {t} (G : R Bool) E (U : block t) : block t :=  
              match E with               
                | RTL.effect_guard guard L => 
                    x <- bind_expr _ (!G && guard)%expr;                     
                    List.fold_right
                        (fun e acc => compile x e acc                                       
                        ) U L
                | RTL.effect_reg_write t var val => 
                    [< r, g, acc >] :- U; _
                | RTL.effect_regfile_write n t var adr val => 
                    [< r, g, acc >] :- U; _ 
                                  end in _). 
  (* reg write *)
  refine (let old := Tuple.get _ _ var acc in _). 
  inversion old. subst.
  refine (we <- bind_expr _ (!X0 || !G)%expr ; 
          w <- bind_expr _ (Emux _ _ (!X0) (!X) (!val) )%expr ; 
          & (Tuple.set var (effect_reg_write _ w we) acc )
         ).

  (* regfile write *)
  refine (let old := Tuple.get _ _ var acc in _). 
  inversion old. subst.   
  refine 
    (
      we <- bind_expr _ (!X1 || !G)%expr; 
      wadr <- bind_expr _ (Emux _ _ (!X1) (!X0) (!adr)); 
      wdata <- bind_expr _ (Emux _ _ (!X1) (!X) (!val)); 
      & (Tuple.set var (effect_regfile_write _ _ wdata wadr we) acc)
    )%expr. 

  refine (true <- bind_expr _ (#b true); 
          compile true E B
         )%expr. 
  Defined. 
    
  let compile := fix compile B :=
      match B with 
        | RTL.telescope_end E 
     
                   
  induction B. 
  refine (acc :- B; _). 
  


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

