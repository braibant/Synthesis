Require Common Core RTL.

Section t. 
  Variable Phi : Core.state. 
  Notation updates := (Common.DList.T (Common.comp option  Core.eval_sync) Phi). 
  
  Section defs. 
    Import Core Common.
    
    Inductive Var (t : type) := box : nat -> Var t. 
    
    Notation expr := (RTL.expr Phi Var). 
    Notation effect := (RTL.effect Var). 
    
    Record block t := mk
      {
        bindings : list ({t : type & expr t});
        value : Var t;
        guard : Var B;
        effects : DList.T (option ∘ effect) Phi
      }. 
              
    Definition compile t (b : RTL.block Phi Var t) : block t. 
    refine (let fold := fix fold t (b : RTL.block Phi Var t) (acc : list ({t : type & expr t})): block t :=
                match b with 
                    RTL.telescope_end x => 
                      match x with 
                          (r,g,e) => mk _ acc r g e
                      end
                  | RTL.telescope_bind a b k => 
                      let n := List.length acc in 
                      let acc := List.app acc [(existT _ a b)] in 
                        fold _ (k (box a n)) acc
                end in fold t b nil). 
    Defined. 

    Definition Env := list {t : type & eval_type t}. 
    Definition eval_binding t (b : expr t) (env : Env) : option Env. 
    Admitted. 
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
    Definition eval_effect  (env : Env) (a : sync)  :
        (option ∘ effect) a ->
        eval_sync a -> (option ∘ eval_sync) a -> option ((option ∘ eval_sync) a).
       refine (fun  eff => 
              match eff with 
                | Some eff =>  
                    match eff in RTL.effect _ s return eval_sync s -> (option ∘ eval_sync) s ->
                                                        option ((option ∘ eval_sync) s)  with 
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
    
    Definition eval_effects (env : Env) (e : DList.T (option ∘ effect) Phi) (Delta : updates) : option updates.  
    refine (Common.DList.map3o _ Phi e st Delta).
    apply (eval_effect env). 
    Defined. 
    
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
End t.  

Notation "[ e : t ]" := (existT _ t e). 
Notation "[ 'read' v : t ]" := (existT _ _ (RTL.Eread _ _ t v)).
Notation "[ 'read' v @ a : t ]" := (existT _ _ (RTL.Eread_rf _ _ _ t  v a)).
Notation W n:= (Core.Tint n). 
Notation "< >" := (Core.Ttuple nil). 
Notation "< a ; .. ; b >" := (Core.Ttuple (a :: .. (b :: nil) ..))%list. 
Notation "# a " := (box _ a) (no associativity, at level 71). 
Notation "f @@ args" := (RTL.Ebuiltin _ _ _ _ f args) (no associativity, at level 71). 
Notation "$ x" := (RTL.Econstant _ _ _ x) (no associativity, at level 71). 
Notation nth v e := (RTL.Enth _ _ _ _ v e). 

Notation "[: x < 2^ n ]" := (Word.mk n x _). 
