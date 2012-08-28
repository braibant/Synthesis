Require Import Common DList FirstOrder. 
Require BDD. 

(**  We start by defining a poor man's operations on set of natural numbers *)
Section attic. 
  Fixpoint mem n l := 
    match l with 
      | nil => false 
      | cons t q => NPeano.Nat.eqb n t || mem n q 
    end%bool.
  

  Fixpoint union (i j: list nat) : list nat :=
    match i with 
      | nil => j
      | t :: q => if mem t j then union q j else union q (t :: j)
    end%list. 
End attic. 
Require  MSets. Require Orders.
Print Orders.OrderedType. 
Module N := OrdersEx.Nat_as_OT. 
Module NS := MSetAVL.Make(N).

Section t. 
  Variable Phi: Core.state.  
  
  (** Recall that in [FirstOrder] syntax, a Var is just a pair of a [type] and a [nat] *)
  Definition Var_eqb {t} (x: Var t) t'  (y: Var t') : bool :=
    (Core.type_eqb t t' && let (x) := x in let (y) := y in (NPeano.Nat.eqb x y))%bool. 

  Notation "x ?= y" := (Var_eqb x _ y) (at level 30).  
  Definition unbox {t} (v:  Var t) := let (x) := v in x.
  Notation "! x" := (unbox x) (at level 80).
  Notation "[::]" := (NS.empty).
  Notation "[:: x ; .. ; y ]" := (NS.add x .. (NS.add y NS.empty) ..).

  (** We define what it means for an expression to use a given variable *)
  Definition used_expr {t} (x: RTL.expr Phi Var t) : NS.t :=
    match x with
      | RTL.Evar t' m => NS.singleton (!m)
      | RTL.Eread t x => [::]
      | RTL.Eread_rf n t x x0 => [::]
      | RTL.Ebuiltin tys res f args => DList.fold (fun _ x acc => NS.add (!x) acc  )  args [::]
      | RTL.Econstant ty x => [::]
      | RTL.Emux t c l r => [:: !c; !l; !r]
      | RTL.Efst l t x => [:: !x ]
      | RTL.Esnd l t x => [:: !x ]
      | RTL.Enth l t v x => [:: !x ]
      | RTL.Etuple tys args => DList.fold (fun _ x acc => NS.add (!x) acc  )  args [::]
    end%bool.

  Notation Gamma := (list ({t: Core.type & RTL.expr Phi Var t})). 
  
  (** [get map x] tries to associate the index of [x] in the substitution [map]*)
  Definition get {t} map (x: Var t) := 
    let (x) := x in
      (do x <- BDD.assoc NPeano.Nat.eqb x map; 
       Some  (box t x)). 

  (** [subst_expr map e] applies the subsitution [map] to the expression [e] *)
  Definition subst_expr (map: list (nat * nat)) {t} (e: RTL.expr Phi Var t) :
    option (RTL.expr Phi Var t) :=
    let get {t} x := get map x in 
    match e in RTL.expr _ _ t return option (RTL.expr Phi Var t)with
      | RTL.Evar t' m => 
          do m <- get m; 
          Some (RTL.Evar m)
      | RTL.Eread t x => Some (RTL.Eread  x)
      | RTL.Eread_rf n t v adr => 
          do adr <- get adr;
          Some (RTL.Eread_rf v adr)
      | RTL.Ebuiltin tys res f args => 
          do args <- DList.mapo (@get) args;
          Some (RTL.Ebuiltin f args)          
      | RTL.Econstant ty x => Some (RTL.Econstant x)
      | RTL.Emux t c l r => 
          (do c <- get c; do l <- get l; do r <- get r; 
           Some (RTL.Emux c l r))
      | RTL.Efst l t x => 
          do x <- get x;
          Some (RTL.Efst x)
      | RTL.Esnd l t x =>
          do x <- get x;
          Some (RTL.Esnd x)
      | RTL.Enth l t v x => 
          do x <- get x;
          Some (RTL.Enth v x)
      | RTL.Etuple tys args =>
          do args <- DList.mapo (@get) args;
          Some (RTL.Etuple args)          
    end%bool.
  
  (** [ise_used n G] tests whether the variable [n] is used in the bindings [G]  *)
  Definition is_used {t}(x:Var t) s := NS.mem (!x) s.

  (** [crop preserve _ _ map G] sift through the bindings [G] to remove
  the unused ones, and accumulates a substitution [map] that is used
  to update the bindings that are kept.  *)

  Section crop. 
    Variable preserve: NS.t.
 
    Fixpoint crop old next (map: list (nat * nat)) (G: Gamma) : option (list (nat * nat) * Gamma) :=
      match G with 
        | nil => Some ((old, next) :: map, nil)
        | cons (existT t e) q => 
            if (NS.mem old preserve) 
            then 
              do e <- (subst_expr map e);
              do map, q <- crop (S old) (S next) ((old,next) :: map) q;
              Some (map,cons (existT _ t e) q)
            else
              crop (S old) (next) ((old,next) :: map) q
    end%bool.
  End crop. 

  Notation Xi := (DList.T (option ∘ RTL.effect Var) Phi). 

  Definition subst_effect {t} (map: list (nat * nat)) (e: RTL.effect Var t):
    option (RTL.effect Var t) :=
    (match e  with
       | RTL.effect_reg_write t value guard =>
           do value <- get map value;
           do guard <- get map guard;
           Some (RTL.effect_reg_write _ (t) value guard)
       | RTL.effect_regfile_write n t value adr guard =>
           do value <- get map value;
           do guard <- get map guard;
           do adr <- get map adr;
           Some (RTL.effect_regfile_write _ _ _ value adr guard)
     end). 

  (** [subst_effect map dl] applies the substitution [map] on every
  element of [dl] *)

  Definition subst_effects (map: list (nat * nat)) (dl: Xi) : option Xi :=
    DList.mapo (fun x dx =>
                  let t :=  comp option (RTL.effect Var) x in  
                    match dx : t return option t with
                    | Some e => do x <- (subst_effect map e); Some (Some x)
                    | None => Some None
                  end) dl. 

  (** [used e] gather the set of variables used by the effect [e]   *)
  Definition used_effect {t} (e: RTL.effect Var t) := 
    match e with 
      | RTL.effect_reg_write _ v g => [:: !v;!g] 
      | RTL.effect_regfile_write _ _ v a g =>
          [:: !v; !g; !a]
    end. 
      
  (** [used_effects x l] gather the set of variables used by the
  effects in [x], and adds it to the set represented by [l] *)

  Definition used_effects (x : Xi) l :=
    DList.fold (fun _ e acc => 
            match e with 
                None => acc 
              | Some e => NS.union (used_effect e) acc
            end) x l. 

  Fixpoint used (G : Gamma) n acc := 
    match G with
      | nil => acc
      | cons (existT _  t ) q => 
          let acc :=  (used q  (S n) acc) in
            if NS.mem n acc then NS.union (used_expr t) acc else acc
    end.
  
            
  
  Definition compile {t} (b: block Phi t) :=
    let (guard) := guard _ _ b in 
    let (value) := value _ _ b in 
    let effects := effects _ _ b in 
    let preserve := used_effects (effects) [:: guard;value] in
      let preserve := used (bindings _  _ b) 0 preserve in 
    do map, bindings <- crop preserve 0 0 nil (bindings _ _ b);
    do guard <- BDD.assoc NPeano.Nat.eqb guard map;
    do value <- BDD.assoc NPeano.Nat.eqb value map;
    do effects <- subst_effects map effects;
    Some (mk Phi t bindings (box _ value) (box _ guard) effects).
End t. 
  