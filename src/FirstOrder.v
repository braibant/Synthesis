(** * Synthesis.FirstOrder : First-order representation of RTL *)

Add Rec LoadPath "." as Synthesis. 
Require Import Common DList. 
Require Core Equality. 

Require Import Eqdep. 

(** This file describes our first order representation of the RTL
language. For now, the transformation from RTL to this language is not
proved. 

 In this firstorder representation, everything ends up being
represented as packed bytes: a type is the size of the bus *)
Notation type := nat (only parsing). 

(** A wire is a singleton inductive *)
Inductive wire (t:type) := box : nat -> wire t. 

(** The type of memory elements depend on the bus size*)
Inductive mem := 
| Tinput : type -> mem 
| Treg : type -> mem
| Tregfile :  nat -> type -> mem. 

(* The denotation of a memory element is a word *)
Fixpoint eval_mem s : Type := 
  match s with
    | Tinput t => Word.T t
    | Treg t => Word.T t
    | Tregfile n t => Regfile.T n (Word.T t)
  end. 

(* An helper function to compute the size of a bus *)
Fixpoint sum l : nat :=
  match l with 
    | nil => 0
    | cons t q => t + sum q 
  end. 

Section t. 
  Context {Phi : list mem}. 
  Inductive expr : type -> Type :=
  | E_var : forall t, wire t -> expr t
  | E_input : forall t, var Phi (Tinput t) -> expr t
  | E_read : forall t,  var Phi (Treg t) -> expr t
  | E_read_rf : forall n t (rf: var Phi (Tregfile n t))(adr: wire n),  expr t 
  | E_andb : wire 1 -> wire 1 -> expr 1
  | E_orb : wire 1 -> wire 1 -> expr 1
  | E_xorb : wire 1 -> wire 1 -> expr 1
  | E_negb : wire 1 -> expr 1
  | E_eq : forall n, wire n -> wire n -> expr 1
  | E_lt : forall n, wire n -> wire n -> expr 1
  | E_le : forall n, wire n -> wire n -> expr 1
  | E_mux : forall n, wire 1 -> wire n -> wire n -> expr n
  | E_plus : forall n, wire n -> wire n -> expr n 
  | E_minus : forall n, wire n -> wire n -> expr n 
  | E_low : forall n m, wire (n + m) -> expr n
  | E_high : forall n m, wire (n + m) -> expr m
  | E_combineLH : forall n m, wire n -> wire m -> expr (n + m)
  | E_constant : forall n, Word.T n -> expr n
  | E_nth: forall l t, var l t -> wire (sum l) -> expr t
  | E_concat: forall l, DList.T wire l -> expr (sum l). 

  Require RTL. 
  Inductive effect : mem -> Type :=
    reg_write : forall t,
                  wire t ->
                  wire 1 -> effect (Treg t)
  | regfile_write : forall (n : nat) (t : type),
                      wire t ->
                      wire n ->
                      wire 1 ->
                      effect (Tregfile n t).
  
  Record block := mk
                    {
                      t : nat;
                      bindings : list ({t : type & expr t});
                      value : wire t;
                      guard : wire 1;
                      effects : DList.T (option ∘ effect) Phi
                    }. 

  Definition Env := list {t : type & Word.T t}. 

  Definition get (env: Env) {t} (x: wire t) : option (Word.T t):=
    let (x) := x in 
    do y <- List.nth_error env x; 
      let (t', y) := y in 
      match NPeano.Nat.eq_dec t t' with
        | left e => 
          eq_rect_r (fun t : type => option (Word.T t)) (Some y)  e
        | right _ => None
      end. 
  (*
  Notation "[ env # x ]" := (get env x). 
  Definition eval_expr (st: DList.T eval_mem Phi) t (e : expr t) (env : Env) : option (Word.T t). 
    refine (match e with
      | E_var t x => [env # x]
      | E_input t x => Some (DList.get x st)
      | E_read t x => Some (DList.get x st)
      | E_read_rf n t rf adr => 
        let rf := DList.get rf st in 
        do adr <- [env # adr];
        Some (Regfile.get rf adr) 
      | E_andb a b => do a <- [env # a]; 
                     do b <- [env # b]; 
                     Some (Word.andb a b)
      | E_orb a b => do a <- [env # a]; 
                     do b <- [env # b]; 
                     Some (Word.orb a b)
                         
      | E_xorb a b => do a <- [env # a]; 
                     do b <- [env # b]; 
                     Some (Word.xorb a b)
      | E_negb x => do x <-  [env # x]; Some (Word.negb x)
      | E_eq n a b => do a <- [env # a]; 
                     do b <- [env # b]; 
                     Some (Word.of_bool (Word.eqb a b))
      | E_lt n a b => do a <- [env # a]; 
                     do b <- [env # b]; 
                     Some (Word.of_bool (Word.lt a b))
      | E_le n a b => do a <- [env # a]; 
                     do b <- [env # b]; 
                     Some (Word.of_bool (Word.le a b))
      | E_mux n c l r => 
        do c <- [env # c]; 
        do l <- [env # l]; 
        do r <- [env # r]; 
        Some (if Word.eqb c (Word.of_bool true) then l else r)
      | E_plus n a b => do a <- [env # a]; 
                       do b <- [env # b]; 
                       Some (Word.add a b)
      | E_minus n a b => do a <- [env # a]; 
                        do b <- [env # b]; 
                        Some (Word.sub a b)
                             
      | E_low n m x => do x <- [env # x]; 
                      Some (Word.low n m x)
      | E_high n m x => do x <- [env # x]; 
                       Some (Word.high n m x)
      | E_combineLH n m a b => do a <- [env # a]; 
                              do b <- [env # b]; 
                              Some (Word.combineLH n m a b)
      | E_constant n x => Some  x
      | E_nth l t m x => 
        (
          do y <- [env # x]; 
          let fold := 
              fix fold t l (m: var l t) (y : Word.T (sum l)) : option (Word.T t) :=
                match m in var l t return Word.T (sum l) -> option (Word.T t)with
                  | var_0 E t => fun y => Some (Word.low t (sum E) y)
                  | var_S E t t' x => fun y => fold _ _ x (Word.high _ _ y)
                end y in fold t l m y        
        )
      | E_concat l x =>
        let fold := 
            fix fold l (dl: DList.T wire l) : option (Word.T (sum l)) :=
                  match dl with
                    | DList.nil => Some (Word.repr 0 0)
                    | DList.cons t q dt dq =>
                      do x <- [env # dt];
                    do y <- fold q dq; 
                    Some (Word.combineLH _ _ x y)
                  end
        in 
        fold l x
            end). 
  Defined.  *)
End t. 
Implicit Arguments expr [].
Arguments expr Phi _. 


Fixpoint compile_type (t : Core.type) :  type :=
  match t with 
    | Core.Tunit => 0
    | Core.Tbool => 1
    | Core.Tint n => n
    | Core.Ttuple l => sum (List.map compile_type l)
  end.

Definition compile_mem s :=
  match s with 
    | Core.Tinput t => Tinput (compile_type t)
    |  Core.Treg t => Treg (compile_type t)
    | Core.Tregfile n t => Tregfile n (compile_type t)
  end. 

Inductive Var (t: Core.type) :  Type := Box : nat -> Var t. 

Section s. 
  (** From [Synthesis.RTL] to the first-order representation. *)
  Definition wire_of_Var {t} (v: Var t) : wire (compile_type t) := 
    let (n) := v in box (compile_type t) n. 
  
  Notation "! x" := (wire_of_Var x) (at level 60). 
  Notation "[ l @1]" := (! (DList.hd l)). 
  Notation "[ l @2]" := (! (DList.hd (DList.tl l))). 
  Notation "[ l @3]" := (! (DList.hd (DList.tl (DList.tl l)))). 

  
  Definition compile_constant :=
    fix compile_constant (ty : Core.type) (c : @Core.Generics.constant _ Core.eval_type ty) : Word.T (compile_type ty) := 
    match ty return Core.Generics.constant ty -> Word.T (compile_type ty) with 
      | Core.Tunit => fun _ => Word.repr 0 0
      | Core.Tbool => fun (x: bool) => if x then Word.repr 1 1 else Word.repr 1 0
      | Core.Tint n => fun x => x
      | Core.Ttuple l => fun x => 
                          let fold :=
                              fix fold l : Core.Generics.constant (Core.Ttuple l) -> 
                                           Word.T (compile_type (Core.Ttuple l)):= 
    match l with 
      | nil => fun x => Word.repr 0 0
      | cons t q => fun x =>  Word.combineLH _ _ 
                                           (compile_constant t (fst x)) 
                                           (fold q (snd x))
    end
                          in 
                          fold l x                            
    end c. 

  Definition compile_expr Phi t (e: RTL.expr Phi Var t) :
    expr (List.map compile_mem Phi) (compile_type t):= 
    match e with 
      | RTL.Einput t v => E_input (compile_type t) (var_map compile_mem Phi _ v)
      | RTL.Evar t v => E_var (compile_type t) (! v) 
      | RTL.Eread t m =>  E_read _ (var_map compile_mem Phi _ m)
      | RTL.Eread_rf n t m adr => E_read_rf n _ (var_map compile_mem Phi _ m) (! adr)
      | RTL.Eandb a b => E_andb (!a) (!b) 
      | RTL.Eorb  a b  => E_orb (!a) (!b) 
      | RTL.Exorb  a b  => E_xorb (!a) (!b) 
      | RTL.Enegb  a  => E_negb (!a)
      | RTL.Eeq t a b => E_eq _ (!a) (!b) 
      | RTL.Elt n a b => E_lt _ (!a) (!b) 
      | RTL.Ele n a b => E_le _ (!a) (!b) 
      | RTL.Eadd n  a b => E_plus _ (!a) (!b)
      | RTL.Esub n  a b => E_minus _ (!a) (!b)
      | RTL.Elow n m a => E_low n m (!a)
      | RTL.Ehigh n m a => E_high n m (!a)
      | RTL.EcombineLH n m a b => E_combineLH n m (!a) (!b)
      | RTL.Econstant ty c => E_constant _ (compile_constant _ c)
      | RTL.Emux t cond l r => E_mux _ (!cond) (!l) (!r)
      | RTL.Efst l t v => E_low _ _ (!v)
      | RTL.Esnd l t v => E_high _ _ (!v)
      | RTL.Enth l t m arg =>  
        E_nth (List.map compile_type l) (compile_type t)
              (var_map compile_type l t m) (!arg)
      | RTL.Etuple l dl => E_concat (List.map compile_type l)
                                   (DList.dmap Var wire compile_type
                                               (fun (x : Core.type) (H : Var x) => !H) l dl)
    end. 
  Definition compile_effect s (e : RTL.effect Var s) : effect (compile_mem s) :=  
    match
      e in (RTL.effect _ s)
      return (effect (compile_mem s))
    with
      | RTL.effect_reg_write t data we =>
        reg_write (compile_type t) (!data) (!we)
      | RTL.effect_regfile_write n t data adr we =>
        regfile_write
          (compile_type (Core.Tint n))
          (compile_type t) 
          (!data) (!adr) (!we)
    end. 
  
  Definition compile_effects Phi (e : RTL.effects Phi Var) : DList.T (option ∘ effect) (List.map compile_mem Phi) :=
    DList.dmap _ _ compile_mem (fun s o => 
                                   match o with 
                                     | Some ef => Some (compile_effect _ ef)
                                     | None => None
                                   end
                                ) Phi e. 

  Definition compile Phi t (b : RTL.block Phi Var t) : @block (List.map compile_mem Phi) . 
    refine (
        let Phi' := List.map compile_mem Phi in 
        let fold := fix fold t (b : RTL.block Phi Var t) (acc : list ({t : type & expr Phi' t})): 
                      @block Phi' :=
                      match b with 
                          RTL.telescope_end x => 
                          match x with 
                              (r,g,e) => mk (compile_type t) acc (! r) (! g) (compile_effects Phi e)
                          end
                        | RTL.telescope_bind t expr k => 
                          let n := List.length acc in 
                          let el :=  existT _ (compile_type t) (compile_expr Phi t expr) in 
                          let acc := List.app acc [el]
                          in 
                          fold _ (k (Box _ n)) acc
                      end in fold t b nil). 
  Defined. 
End s. 
  


(* Theorem compile_correct Phi t (b : RTL.block Phi Var t) state : *)
(*   forall Delta, *)
(*     (RTL.Eval Phi state b Delta) == Eval   *)
(*
Definition Env := list {t : type & eval_type t}. 
Definition eval_binding t (b : expr t) (env : Env) : option Env. Admitted. 

Fixpoint eval_bindings (l : list {t : type & expr t}) acc : option Env :=
  match l with 
      nil => Some acc
    | cons (existT t b) q => 
      do b <- eval_binding t b acc;            
        let acc := List.app acc b in 
        eval_bindings q acc
  end. 


    Definition lookup t (v : Var t) (l : Env) : option (eval_type t).
    refine (let (n) :=  v in 
              do x <- List.nth_error l n; 
              match x with 
                | existT t' x =>
                    (if type_eqb t t' as b return (type_eqb t t' = b -> option (eval_type t))
                     then fun H : type_eqb t t' = true =>                             
                            eq_rect_r (fun t0 : type => option (eval_type t0)) (Some x)
                                      (type_eqb_correct t t' H)
                     else fun _ => None) eq_refl
                     end
           ). 
    Defined. 



    Variable st : eval_state Phi.
    Definition eval_effect  (env : Env) (a : mem)  :
        (option ∘ effect) a ->
        eval_mem a -> (option ∘ eval_mem) a -> option ((option ∘ eval_mem) a).
       refine (fun  eff => 
              match eff with 
                | Some eff =>  
                    match eff in RTL.effect _ s return eval_mem s -> (option ∘ eval_mem) s ->
                                                        option ((option ∘ eval_mem) s)  with 
                      |  RTL.effect_reg_write t val we => 
                           fun _ old => 
                             match old with 
                               | Some _ => Some old
                               | None => 
                                   do we <- lookup _ we env;
                                   do val <- lookup _ val env;
                                   Some (if we then Some val else None)
                             end
                      |  RTL.effect_regfile_write n t val adr we => 
                           fun rf old =>
                             match old with 
                               | Some _ => Some old 
                               | None => 
                                   do we <- lookup _ we env;
                                   do val <- lookup _ val env;
                                   do adr <- lookup _ adr env;
                                   Some (if we then 
                                     let rf := Regfile.set rf adr val in
                                       Some rf
                                   else
                                     None)
                             end
                    end
              | None => fun _ old => Some old            
              end). 
    Defined. 
    
    Definition eval_effects (env : Env) (e : DList.T (option ∘ effect) Phi) (Delta : updates) : 
      option updates :=
      DList.map3o (eval_effect env) Phi e st Delta.

    
    Definition eval_block t (b : block t) (Delta : updates) : 
      option (option (eval_type t * updates)). 
    refine (
        match b with
          | {| bindings := bindings; value := value; guard := guard; effects := effects |} =>
              do env <- eval_bindings bindings [];
              do guard <- lookup _ guard env;  
              do value <- lookup _ value env;  
              do effects <- eval_effects env effects Delta; 
              Some (if guard then 
                      Some (value, effects)
                    else None )end)%list.  
    Defined. 
End defs.
*)

Notation "[ e : t ]" := (existT _ t e). 
Notation "[ 'read' v : t ]" := (existT _ _ (RTL.Eread _ _ t v)).
Notation "[ 'read' v @ a : t ]" := (existT _ _ (RTL.Eread_rf _ _ _ t  v a)).
Notation W n:= (Core.Tint n). 
Notation "< >" := (Core.Ttuple nil). 
Notation "< a ; .. ; b >" := (Core.Ttuple (a :: .. (b :: nil) ..))%list. 
Notation "# a " := (box _ a) (no associativity, at level 71). 
Notation "$ x" := (RTL.Econstant _ _ _ x) (no associativity, at level 71). 
Notation nth v e := (RTL.Enth _ _ _ _ v e). 

Notation "[: x < 2^ n ]" := (Word.mk n x _). 
