Require Common Core RTL.

(** First, we transform the Flat language into RTL3  *)

Module RTL3. 
  Section t. 
    Variable Phi : Core.state. 
    
    Notation updates := (Common.Tuple.of_list (Common.comp option  Core.eval_sync) Phi). 
    
    Section defs. 
      Import Core Common. 
      Variable Var : type -> Type. 
      
      Inductive expr : type -> Type :=
      | Ebuiltin : forall (args : list type0) (res : type0),
                     builtin args res ->
                     DList.T (fun j : type0 => Var (Tlift j)) args ->
                     expr (Tlift res)
      | Econstant : forall ty : type0, constant0 ty -> expr (Tlift ty)
      | Emux : forall t : type,
                  Var Bool ->  Var t -> Var t -> expr  t
      | Efst : forall (l : list type) (t : type),
                 Var (Ttuple (t :: l)) -> expr t
      | Esnd : forall (l : list type) (t : type),
                 Var (Ttuple (t :: l)) -> expr (Ttuple l)
      | Enth : forall (l : list type) (t : type),
                 var l t -> Var (Ttuple l) -> expr t
      | Etuple : forall l : list type,
                   DList.T (Var) l -> expr  (Ttuple l). 
      
      (** Combinational bindings (expressions, register reads)  *)
      Inductive bind (t : type) : Type := 
      | bind_expr :  expr t ->  bind t
      | bind_reg_read : var Phi (Treg t) -> bind t
      | bind_regfile_read : forall n, var Phi (Tregfile n t) -> Var (Tlift (Tint n)) -> bind t. 
    
      Inductive telescope (A : Type): Type :=
      | telescope_end : A -> telescope A
      | telescope_bind : forall arg, bind arg -> (Var arg -> telescope A) -> telescope A. 
      
      
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
      | effect_reg_write : forall t,  Var t -> Var Bool -> effect (Treg t)
      | effect_regfile_write : forall n t,  Var t -> Var (Tlift (Tint n)) -> Var Bool -> 
                                       effect (Tregfile n t). 
      
      Definition effects := Tuple.of_list (option ∘ effect) Phi. 

      Definition block t := telescope (Var t * Var Bool *  effects). 
      Notation "x :- e1 ; e2" := (telescope_bind  _ _ (bind_expr _ e1) (fun x => e2)) (right associativity, at level 80, e1 at next level).  
      Notation "x <- e1 ; e2" := (telescope_bind  _ _ (e1) (fun x => e2)) (right associativity, at level 80, e1 at next level).  
      Notation " & e " := (telescope_end _  e) (at level 71). 


      Definition compile_expr t (e : Core.expr Var t) : telescope (Var t).
      refine (
          let fix fold t (e : Core.expr Var t) :=
              let fix of_list0 (l : list type0) (x : DList.T (fun j => Core.expr Var (Tlift j)) l) : telescope (DList.T (fun j => Var (Tlift j)) l) :=                 
                  match x in  (DList.T _ l)
                     return
                     (telescope (DList.T (fun j : type0 => Var (Tlift j)) l)) with
                    | DList.nil => & ([])%dlist
                    | DList.cons t q dt dq => 
                        x  :-- fold (Tlift t) dt;
                        dq :--   of_list0 q dq;   
                        &  ((x : (fun j => Var (Tlift j)) t ) :: dq)%dlist
                  end in
                let fix of_list (l : list type) (x : DList.T (Core.expr Var) l) : telescope (DList.T Var l) :=
                    match x in  (DList.T _ l)
                       return
                       (telescope (DList.T Var l)) with 
                      | DList.nil => & ([])%dlist
                      | DList.cons t q dt dq => 
                          x  :-- fold t dt;
                          dq :--   of_list q dq;   
                          &  (x :: dq)%dlist
                    end in

                  match e with
                  | Core.Evar t v => & v
                  | Core.Ebuiltin args res f x => 
                      x :-- of_list0 args x; 
                      y :- Ebuiltin args res f x; 
                      &y 
                  | Core.Econstant ty c => c :- Econstant _ c; &c
                  | Core.Emux t c l r => 
                      c :-- fold _ c;
                      l :-- fold _ l;
                      r :-- fold _ r;
                      ret :- (Emux t c l r) ;
                      & ret
                  | Core.Efst l t x => 
                      x :-- fold _ x; ret :- Efst l t x; & ret
                  | Core.Esnd l t x => 
                      x :-- fold _ x; ret :- Esnd l t x; & ret
                  | Core.Enth l t m x => 
                      x :-- fold _ x; ret :- Enth l t m x; & ret
                | Core.Etuple l exprs => 
                    exprs :-- of_list l exprs; ret :- Etuple l exprs; &ret
                end in fold t e).
      Defined. 
      
      Definition compile_effects (e : RTL.effects Phi Var)  : effects. 
      unfold effects. refine  (Tuple.map _ Phi e).
      intros a x.
      refine (match x with
                  | None => None
                  | Some x => match x with 
                                 | RTL.effect_reg_write t v g => 
                                     Some (effect_reg_write t v g)
                                 | RTL.effect_regfile_write n t v adr g =>
                                     Some (effect_regfile_write n t v adr g)
                             end
              end).
      
      Defined. 

      Definition compile t  (b : RTL.block Phi Var t) : block t. 

      refine (let fold := fix fold t (b : RTL.block Phi Var t) : block t :=
                  match b with 
                    | RTL.telescope_end x => 
                        match x with 
                            (r, g,e) => g :-- compile_expr _ g; & (r,g,compile_effects e)
                        end
                    | RTL.telescope_bind a bd k => 
                        match bd with
                          | RTL.bind_expr x => 
                              x :-- compile_expr _ x ; fold _ (k x)
                          | RTL.bind_reg_read x => 
                              x <- bind_reg_read _ x; fold _ (k x)
                          | RTL.bind_regfile_read n x x0 => 
                              x <- bind_regfile_read _ n x x0; fold _ (k x)
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
              | Ebuiltin args res f exprs => 
                  let exprs := 
                      Common.DList.to_tuple  
                           (fun (x : Common.type0) (X : Core.eval_type (Core.Tlift x)) => X)
                           exprs
                  in
                    Common.builtin_denotation args res f exprs
              | Emux t b x y => if b then x else y 
              | Econstant ty c => c
              | Etuple l exprs => 
                  Common.DList.to_etuple (fun _ X => X) exprs
              | Enth l t v e => 
                  Common.ETuple.get l t v e
              | Efst l t  e => 
                  Common.ETuple.fst _ _ e
              | Esnd l t  e => 
                  Common.ETuple.snd _ _ e
          end 
      in eval_expr t e).  
    Defined. 

    Definition eval_bind t (b : bind Core.eval_type t) : (Core.eval_type t).
    refine (match b with
              | bind_expr x =>  (eval_expr _ x)
              | bind_reg_read v => (Common.Tuple.get _ _ v st)
              | bind_regfile_read n v adr => 
                  let rf := Common.Tuple.get Phi (Core.Tregfile n t) v st in
                    Common.Regfile.get rf (adr)                
            end
           ). 
    Defined. 
                                                                   
    Definition eval_effects (e : effects Core.eval_type) (Delta : updates) : updates.  
    unfold effects in e. 

    (* refine (Tuple.fold Phi _ e Delta).  *)
    refine (Common.Tuple.map3 _ Phi e st Delta). 
    Import Common Core.
    Definition eval_effect (a : Core.sync) :   
      (Common.comp option (effect Core.eval_type)) a ->
      Core.eval_sync a -> (Common.comp option Core.eval_sync) a -> (Common.comp option Core.eval_sync) a. 
    
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

  Fixpoint eval_telescope { A B} (F : A -> B) (T : telescope  eval_type A) :=
    match T with 
      | telescope_end X => F X
      | telescope_bind arg bind cont =>
          let res := eval_bind arg bind in 
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
  
  Require Import Equality Bool.
  
  Lemma compile_effects_correct Phi st   e : 
    forall Delta, 
      eval_effects Phi st (compile_effects Phi Core.eval_type e) Delta =
                   RTL.eval_effects Phi st e Delta. 
  Proof. 
    induction Phi. simpl. auto. 
    simpl; intros. destruct e. destruct st. destruct Delta. case_eq c; intros. 
    dependent destruction e2. simpl. 
    destruct c0.    f_equal. apply IHPhi. 
    f_equal. auto. 
    f_equal. auto. 
    f_equal. auto. 
  Qed. 
  
  Hint Resolve compile_effects_correct. 
  Notation "e :-- t1 ; t2 " := (compose _ _  t1 (fun e => t2)) (right associativity, at level 80, e1 at next level).
  Notation "x :- e1 ; e2" := (telescope_bind _ _ _ _ (bind_expr _ e1) (fun x => e2)) (right associativity, at level 80, e1 at next level).  
  Notation "x <- e1 ; e2" := (telescope_bind  _ _ _ _ (e1) (fun x => e2)) (right associativity, at level 80, e1 at next level).  
  Notation " & e " := (telescope_end _   _ _ e) (at level 71). 

  Lemma compiler_correct Phi st t (b : RTL.block Phi Core.eval_type t) : forall Delta, 
        eval_block Phi st t (compile Phi Core.eval_type t b) Delta = RTL.eval_block Phi st t b Delta. 
  Proof. 
      intros.
      induction b.
      simpl. destruct a as [[r g] e]; simpl.
      unfold eval_block. 
      Lemma compile_expr_correct {A B} Phi st t e (f : Core.eval_type t -> telescope _ _ A) (E : A -> B): 
        eval_telescope Phi st E (r :-- compile_expr Phi Core.eval_type t e; f r) = 
        eval_telescope Phi st E (f (Core.eval_expr t e)). 
      revert e.
      induction e. 
      induction e; try reflexivity. simpl. 
      {
        dependent induction g.  simpl; f_equal. destruct v; repeat f_equal. auto. 
        simpl. 

      dependent destruction g. 
      destruct v; repeat f_equal. 
      
      { indu
     }
      
      unfold eval_block. 
(* Solutions:

- use a list of {t : type & x : expr t}, and use the fact that types
   are decidable to be sure lookups work fine

- use one list for each type 

- do not use lists (but loose some sharing)

*)

Notation cst t:= (@Common.constant _ Common.eval_type0 t).
Notation lift t := (Core.Tlift t).  

Inductive sval : Core.type -> Type :=
| SVar: forall t, nat -> sval t
| SConstant : forall t, cst t -> sval (lift t)
| SMux : forall t, sval (lift Common.Tbool) -> sval t -> sval t -> sval t
| STuple : forall l, Common.DList.T (sval) l ->  sval (Core.Ttuple l).


Section t. 
  
  Variable var : Core.type -> Type.
  Notation V := (fun t => var t * sval t)%type. 
  Import Core. 

  
  Definition cse_expr t (e : expr V t) : expr var t * option (sval t). 
  refine (
      let fix fold t (e : expr V t) :=
      match e with
        | Evar t v => (Evar (fst v), Some (snd v))
        | Ebuiltin args res f x => _
        | Econstant ty c => (# c, Some (SConstant _ c))
        | Emux t c l r =>  (Emux _ _ (fst (fold _ c)) (fst (fold _ l)) (fst (fold _ r)), None) 
        | Efst l t x => _
        | Esnd l t x => _
        | Enth l t m x => _
        | Etuple l exprs => _
      end in fold t e). 
  admit.
  
  refine 