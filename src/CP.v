Require Import Common DList Core ZArith. 
Require BDD.

(* In this compilation pass, we implement boolean simplification using BDDs. *)

Section t. 

  Variable Phi : state.   
  Variable Var : type -> Type.

  Inductive toption A : type -> Type :=
  | SNone : forall t, toption A t
  | SSome : forall (b: A), toption A Core.Tbool. 

  Arguments SNone {A} t. 
  Arguments SSome {A} b. 

  Definition bind {A B t} (F: A -> toption B Tbool) (o: toption A t) : toption B t :=
    match o with
        | SNone t => SNone t
        | SSome x => (F x) end. 

  Notation "'do' X <- A ; B" := 
  (bind (fun X => B) A)
    (at level 200, X ident, A at level 100, B at level 200). 

  (* Maybe we have a pointer *)
  Definition sval := toption BDD.expr. 

  Notation V := (fun t => Var t * sval t)%type.   
  
  Inductive bexpr :=
  | Lift : BDD.expr  -> bexpr
  | Ite : forall (c l r : BDD.expr), bexpr
  | And : forall (a b : BDD.expr), bexpr
  | Or : forall (a b : BDD.expr), bexpr
  | Xor : forall (a b : BDD.expr), bexpr
  | Not : forall (a : BDD.expr), bexpr.
  
  (* Maybe we have a boolean expression *)
  Definition bexpro := toption bexpr.   
  
  (* bang := lift Lift *)
  Notation bang := (bind (fun x => SSome (Lift x))). 
  Notation "!!" := (SNone _). 

  Notation bop op dl:= 
  (let a := DList.hd dl in 
   let b := DList.hd (DList.tl dl) in 
     do a <- (snd a);
     do b <- (snd b);
     SSome (op a b)). 

  Require Import RTL. 
  Definition cp_expr t (e : expr Phi V t) : (expr Phi Var t) * (toption bexpr t). 
  refine (match e with
            | Evar t x => 
                match t as ty return V ty -> (expr Phi Var ty) * (toption bexpr ty) with 
                  | Tbool => fun y => (Evar (fst y), bang (snd y)) 
                  | t => fun y  => (Evar (fst y), !!) end x
            | Eread t v => (Eread v, !!)
            | Eread_rf n t v adr => (Eread_rf v (fst adr), !!)
            | Ebuiltin tys res f args  => 
                (Ebuiltin f (DList.map (fun _ x => fst x) args), _)           
            | Econstant t x => 
                match t as ty return constant ty -> (expr Phi Var ty * toption bexpr ty) with
                  | Tbool => fun c => if ( c : bool)
                                    then (Econstant c, SSome (Lift BDD.T))
                                    else (Econstant c, SSome (Lift BDD.F))
                  | t => fun c => (Econstant c, !!) end x
            | Emux ty c l r => 
                (_ ,
                 match ty as t return V t -> V t  -> toption bexpr t with 
                   | Tbool => fun l r =>  
                               (do c <- (snd c);
                                do l <- (snd l);
                                do r <- (snd r);
                                SSome (Ite c l r))
                   | _ => fun _ _ => !! end l r)
            | Efst l t v => (Efst (fst v) , !!)
            | Esnd l t v => (Esnd (fst v) , !!)
            | Enth l t m v => (Enth m (fst v), !!)
            | Etuple l dl => (Etuple (DList.map (fun _ x => fst x) dl), !!)
          end). 
  refine (match f in builtin tys res return DList.T V tys -> toption bexpr res with
            | BI_andb => fun dl =>  bop And dl
            | BI_orb  => fun dl =>  bop Or  dl
            | BI_xorb => fun dl =>  bop Xor dl
            | BI_negb => fun dl =>  do e <- (snd (DList.hd dl)); SSome (Not e)
            | _ => fun _ => !!
          end args); simpl.
  refine (match snd c with 
                   | SSome BDD.T => (Evar (fst l))
                   | SSome BDD.F => (Evar (fst r))
                   |  _ => Emux (fst c) (fst l) (fst r) end).  
  Defined. 

  Record Env := mk
    {
      Ebdd : BDD.BDD;
      Eknown: list (BDD.expr * Var Tbool);
      Enext: nat
    }. 

  Definition empty : Env := mk BDD.empty [] 100. 
  
  Definition add_bdd (Gamma: Env) (b:bexpr ): option (BDD.expr * Env) :=  
    match b with
      | Lift x => Some (x, Gamma)
      | Ite c l r => 
          do r, bdd <- BDD.ite (Ebdd Gamma) c l r;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
      | And a b => 
          do  r,bdd <- BDD.andb (Ebdd Gamma) a b;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
      | Or a b => 
          do  r,bdd <- BDD.orb (Ebdd Gamma) a b;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
      | Xor a b => 
          do r,bdd  <- BDD.xorb (Ebdd Gamma) a b;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
      | Not a => 
          do r,bdd <- BDD.negb (Ebdd Gamma) a;
          Some (r, mk bdd (Eknown Gamma) (Enext Gamma))
    end. 

  Definition lookup (Gamma: Env) (b: BDD.expr) : option (Var Tbool) :=
    BDD.assoc BDD.expr_eqb b (Eknown Gamma). 

  Definition add_env (Gamma: Env) (v:Var Tbool) (b:BDD.expr): Env :=
    mk (Ebdd Gamma) ((b,v) :: Eknown Gamma) (Enext Gamma). 
  
  Definition incr Gamma :=
    let n := (Enext Gamma) in 
    let (r, bdd) := BDD.mk_var (Ebdd Gamma) n in
      (r, mk bdd (Eknown Gamma) (S n)). 

  (* Unfortunately, multiple reads from the same state elements cannot be shared *)
  Fixpoint cp_telescope {A} (Gamma: Env) (T : telescope Phi V A) : telescope Phi Var A :=
    match T with
      | & x => & x
      | telescope_bind arg b cont => 
          let (e,svo) := cp_expr arg b in 
            match svo in toption _ arg return 
               (Var arg * sval arg -> telescope Phi V A) -> 
               expr Phi Var arg -> telescope Phi Var A 
            with 
              | @SNone  arg => 
                  match arg as ty return 
                     (Var ty * sval ty -> telescope Phi V A) -> 
                     expr Phi Var ty -> telescope Phi Var A 
                  with 
                    | Tbool => fun cont e => 
                                (
                                  k :- e; 
                                  let (ptr, Gamma) := incr Gamma in 
                                    let Gamma := add_env Gamma k ptr in
                                      cp_telescope Gamma (cont (k, SSome ptr)))
                    | _ => fun cont e => 
                            k :- e; cp_telescope Gamma (cont (k, SNone _))
                  end
              | SSome sv => 
                  (* We have a symbolic value *)
                  fun cont e =>  
                    match add_bdd Gamma sv with 
                      | Some (ptr, Gamma) =>
                          (* the symbolic value correspond to a pointer in the bdd *)
                          match lookup Gamma ptr with
                            | None =>
                                (* this pointer does not
                                          correspond to a value. We
                                          bind this value, and add it
                                          to the environment*)
                                k :- e;
                                let Gamma := add_env Gamma k ptr in 
                                  cp_telescope Gamma (cont (k, SSome ptr))
                            | Some old => 
                                (* the pointer was already
                                          associated. No need to bind
                                          a new value *)
                                cp_telescope Gamma (cont (old, (SSome ptr))) 
                          end
                      | None => 
                          (* adding to the bdd failed. This
                                    should not happen, but is safe *)
                          k :- e; cp_telescope Gamma (cont (k,SNone _))
                    end
            end cont e
    end. 


  Definition cp_effects (eff: effects Phi V) : effects Phi Var :=
    DList.map
         (fun (a : sync) (x : (option ∘ effect V) a) =>
            match x with
              | Some x0 =>
                  match x0 in (effect _ s) return ((option ∘ effect Var) s) with
                    | effect_reg_write t x1 x2 =>
                        Some (effect_reg_write Var t (fst x1) (fst x2))
                    | effect_regfile_write n t x1 x2 x3 =>
                        Some (effect_regfile_write Var n t (fst x1) (fst x2) (fst x3))
                  end
              | None => None
            end) eff. 
  
  
  Definition cp_block  t (b : block Phi V t) : block Phi Var t :=    
    let b := ( _ :- @Econstant  _ _ Tbool true ;
               _ :- @Econstant  _ _ Tbool false ;
               b) in 
    k :-- cp_telescope empty b;
    match k with (v,g,e) =>
                   & (fst v, fst g, cp_effects  e)
    end. 
End t. 

Definition Compile Phi t (b : Block Phi t) : Block Phi t :=  
  fun V => cp_block Phi V t (b _). 

Theorem Compile_correct Phi t b (Hwf : WF Phi t b): forall st Delta,
  Eval Phi st t (Compile Phi t b) Delta =  Eval Phi st t b Delta. 
Proof. 
Admitted. 