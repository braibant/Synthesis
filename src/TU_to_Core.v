Require Import Common. 
Require Core TaggedUnions. 
Require Import PArith. 
Module S := TaggedUnions.  
Module T := Core. 

Class Eqb (X : Type) := {eqb : X -> X -> bool; 
                         eqb_correct: forall x y, Bool.reflect (x = y) (eqb x y) }. 

Module M. 
  Section t. 
    Context (X : Type) {E : Eqb X}. 
    Definition T := list (positive * X). 
  
    Definition singleton x : T := ([(1%positive,x)])%list. 

    Fixpoint add n x (l : T) : T :=
      match l with 
        | nil => [(n,x)]
        | (m,y)::q => 
            if eqb x y then ((n + m)%positive, x) :: q  else (m,y) :: add n x q
      end%list. 

    Fixpoint max n x (l : T) : T :=
      match l with 
        | nil => [(n,x)]
        | (m,y)::q => 
            if eqb x y then (Pos.max n m, x) :: q  else (m,y) :: add n x q
      end%list. 
    
    Fixpoint union (a b : T) : T :=
      match a with 
        |nil => b 
        | (n,x) :: q => add n x (union q b)
      end%list. 

    Fixpoint join (a b : T) : T :=
      match a with 
        |nil => b 
        | (n,x) :: q => max n x (union q b)
      end%list. 
    
    Fixpoint copy n (x : X)  :=
      match n with 
        | xH => [x]
        | xO m => copy m x ++ copy m x
        | xI m => x :: copy m x  ++ copy m x
      end%list. 

    Fixpoint contents (a : T) := 
      match a with 
        | nil => nil
        | (n,x) :: q => copy n x ++ (contents q)
      end%list.         
    
    Fixpoint elements (a : T) : list X := List.map (@snd _ _) a. 
    
    Fixpoint of_list (l : list X) : T :=
      match l with 
        | nil => nil
        | cons t q => add 1 t (of_list q)
      end. 
  End t. 
  Arguments singleton {X} _. 
  Arguments add {X _} n x l. 
  Arguments union {X _} a b. 
  Arguments join {X _} a b. 
  Arguments of_list {X _} l.  

End M. 

Section compile. 
  Variable Phi : S.state. 

  Instance Ttype_Eqb : Eqb T.type. 
  Admitted. 
  
  Definition flat : S.type -> T.type .
  intros x. 
  Definition open : T.type -> M.T T.type. 
  intros x. 
  refine (
      match x with 
        | T.Tlift t0 => M.singleton (T.Tlift t0)
        | T.Ttuple l => M.of_list l
      end). 
  Defined. 
  refine (
      let f := fix convert (x : S.type) : T.type :=
          match x with 
                  | S.Tlift t0 => T.Tlift t0
                  | S.Ttuple l => T.Ttuple (List.map convert l)
                  | S.Tunion C =>  
                      let l := List.map convert C in 
                      let l := List.map open l in 
                      let m := List.fold_right M.join nil l in 
                      let c := T.Tlift (Tfin (List.length C )) in 
                        T.Ttuple (c:: M.contents _ m)
          end in _). 
  apply (f x). 
  Defined. 
  Definition compile_sync : S.sync -> T.sync. 
  Proof. 
    refine (fun X => match X with
                      |S.Treg t => T.Treg (flat t)
                      |S.Tregfile n t => T.Tregfile n (flat t)
            end). 
  Defined. 
  Definition var_map { A B } (f : A -> B) l (t : A) : var l t -> var (List.map f l) (f t). 
  Admitted. 
  Definition compile_state : S.state -> T.state := List.map compile_sync. 


  Variable (R : T.type -> Type). 

  Definition allocate t l (c : var l t) (x : T.expr R (flat t)) : T.expr R (flat (S.Tunion l)). 
  Proof. 
  Admitted. 

  Definition deallocate t l tr (c : var l t) (e : T.expr R (flat (S.Tunion l))) 
                        (cont : R (flat t) -> T.action (compile_state Phi) R (flat tr)): 
    T.action (compile_state Phi) R (flat tr). 
  Admitted. 
  
  Definition compile_expr t : S.expr (fun x => R (flat x)) t  -> T.expr R (flat t).  

  refine (let compile := fix compile t (e : S.expr (fun x => R (flat x)) t) : T.expr R (flat t) := 
              match e with
                | S.Evar t v => T.Evar v
                | S.Ebuiltin args res f x => _
                | S.Econstant ty c => T.Econstant c
                | S.Efst l t x => T.Efst _ _ _ (compile _ x)
                | S.Esnd l t x => T.Esnd _ _ _ (compile _ x)
                | S.Enth l t m x => T.Enth  (var_map _ _ _ m) (compile _ x) 
                | S.Etuple l exprs => T.Etuple _ _ _ 
                | S.Econstr l t c x => _

              end  
          in compile t
         ). 
  eapply (T.Ebuiltin f). eapply DList.dlist_map.  2: apply x. 
  simpl. intros. apply (compile (S.Tlift x0) X).    
 
   Definition zob {A B} (F : A -> Type) (G: B -> Type) (C : A -> B) (D : forall x, F x -> G ( C x)) (l: list  A) (dl : DList.dlist F l) : DList.dlist G (List.map C l). 
  induction dl. simpl. constructor. 
  simpl. constructor. apply D.  auto. 
  apply IHdl. 
  Defined. 
  
  
  
  eapply (zob _ _ _ compile) in exprs. apply exprs.
  apply (allocate _ _ c (compile _ x)). 
  Defined. 

  Definition fin_of_var {T} l (t : T) : var l t -> Finite.T (List.length l).
  induction 1.
  refine  (Finite.Build_T _ 0 _). simpl. admit.
  refine  (Finite.Build_T _ (S (Finite.val IHX)) _). simpl. admit.
  Defined.

  Definition compile   t : S.action Phi (fun x => R (flat x )) t -> T.action (compile_state Phi ) R (flat t). 
  refine (let compile := fix compile t (a : S.action Phi (fun x => R (flat x)) t) : 
              T.action (compile_state Phi) R (flat t) :=
              match a with
                | S.Return t exp => T.Return (compile_expr _ exp)
                | S.Bind t u a f => T.Bind (compile _ a) (fun X => compile _ (f X))  
                | S.Assert e => T.Assert (compile_expr _ e)
                | S.Primitive args res p exprs => 
                    let exprs := 
                        (zob (S.expr (fun x : S.type => R (flat x))) 
                             (T.expr R) flat compile_expr args exprs)
                    in 
                      T.Primitive (List.map flat args) (flat res) _ exprs
                | S.Try a => T.Try _ _ (compile _ a)
                | S.Case td l t c e x => _
              end
          in compile t
         ). 
  clear exprs0. revert exprs. 
  refine (match p with 
              S.register_read t v => fun exprs =>
                                     (
                                       T.register_read  (var_map compile_sync _ _ v)
                                       :T.primitive (compile_state Phi) (List.map flat []) (flat t))
              
            | S.register_write t v => fun exprs => 
                                     (
                                       T.register_write (var_map compile_sync Phi (S.Treg t) v)
                                       :T.primitive (compile_state Phi) (List.map flat [t])
                                         (flat (S.Tlift Tunit))
                                     )
            | S.regfile_read n t v p => fun exprs => ( T.regfile_read
                                                      (var_map compile_sync Phi (S.Tregfile n t) v) p
                                                     :T.primitive (compile_state Phi)
                                                       (List.map flat [S.Tlift (W p)]) 
                                                       (flat t))
            | S.regfile_write m t v p => fun exprs => 

                                          (   T.regfile_write
                   (var_map compile_sync Phi (S.Tregfile m t) v) p
                 :T.primitive (compile_state Phi)
                    (List.map flat [S.Tlift (W p); t])
                    (flat (S.Tlift Tunit)))
         end ). 
  (* Case case *)
  + apply compile_expr in e.
    Import T. 
    refine (T.Bind (T.Assert _) (fun _ => _)). 
    refine (_  = _ )%expr. 
    eapply Econstant. exact (fin_of_var _ _ c : constant0 (Tfin _)). 
    simpl in e. apply Efst in e. apply e. 
    
    clear _H. set (y := fun e => compile _ (x e)). clearbody y. clear x.  clear - e y c. 
   apply (deallocate _ _ _ c e y). 
  
  Defined. 