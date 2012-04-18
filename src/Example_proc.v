Require Import Common. 
Require Import TRS. 

Definition val := T01 (Tint 16).

Definition reg :=  T01 (Tint 2).  
Definition RF := Tregfile 4 (val). 
Definition instr : type1 := 
  Tunion "instr" ("LOADI"  of (Ttuple [reg ;val]) 
                 :: "LOADPC" of (reg) 
                 :: "ADD" of (Ttuple [reg;reg;reg]) 
                 :: "BZ" of (Ttuple [reg;reg])
                 :: "LOAD" of (Ttuple [reg;reg])
                 :: "STORE" of (Ttuple [reg;reg])
                 :: type1_id_list_nil ). 

Definition IMEM := Tregfile (two_power_nat 16) instr. 
Definition DMEM := Tregfile (two_power_nat 16) val. 
Definition PC := Treg val. 
Definition state := [PC; RF; IMEM; DMEM]. 

Definition trivial_pattern2_vector l : pattern2_vector l l.
induction l. 
constructor. 
apply (pattern2_vector_cons [a] l a l). constructor.  
apply IHl. 
Defined. 

Definition WHERE E F t (p : pattern1 F t) (e : @expr1 E t) : where_clause E (E++F). 
eapply where_clause_cons. 
3: apply where_clause_nil. 
apply p. 
apply e. 
Defined. 
Arguments WHERE {E F t} p%pattern e%expr.

Notation "M  '[' ? key ']' " :=
(Eget_regfile _ _ M _ key)(at level 0, no associativity) : expr_scope. 

Definition IS_LOADI : pattern1 ([Treg reg ; Treg val]) instr.  
apply Punion. apply pattern1_disjunct_hd. apply ( [| Pvar1 reg , Pvar1 val|])%pattern. 
Defined. 

Definition IS_LOADPC : pattern1 ([Treg reg]) instr.  
apply Punion. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_hd. apply Pvar1. 
Defined. 

Definition IS_ADD : pattern1 ([Treg reg; Treg reg; Treg reg]) instr.  
apply Punion. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_hd. apply ([| Pvar1 _ , Pvar1 _, Pvar1 _ |])%pattern. 
Defined. 

Definition IS_BZ : pattern1 ([Treg reg; Treg reg]) instr.  
apply Punion. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_hd. apply ([| Pvar1 _ , Pvar1 _ |])%pattern. 
Defined. 

Definition IS_LOAD : pattern1 ([Treg reg; Treg reg]) instr.  
apply Punion. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_hd. apply ([| Pvar1 _ , Pvar1 _ |])%pattern. 
Defined. 

Definition IS_STORE : pattern1 ([Treg reg; Treg reg]) instr.  
apply Punion. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_tl. 
apply pattern1_disjunct_hd. apply ([| Pvar1 _ , Pvar1 _ |])%pattern. 
Defined. 

(* (pc,rf,imem,dmem) where LOADI(rd,const) = imem[pc]
     –> (pc+1, rf[rd <- const], imem, dmem) *)
Definition loadi_rule : rule state. 
set (env1 := state). 
set (env2 := List.app state  [Treg reg ; Treg val]). 
set (pc := var_0 : var env1 PC). 
set (rf := var_S var_0 : var env1 RF). 
set (imem := var_S (var_S var_0) : var env1 IMEM). 
set (dmem := var_S (var_S (var_S var_0)) : var env1 DMEM). 
set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (const := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg val)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_LOADI (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 
        
refine ([| Eset _ (! (var_lift  pc )+ {< Cword 1>})%expr , [!rd <- !const] , • , • |])%expr2. 
Defined. 


(* (pc,rf,imem,dmem) where LOADPC(rd) = imem[pc]
     –> (pc+1, rf[rd <- pc], imem, dmem) *)

Definition loadpc_rule : rule state. 
set (env1 := state). 
set (env2 := List.app state  [Treg reg]). 
set (pc := var_0 : var env1 PC). 
set (rf := var_S var_0 : var env1 RF). 
set (imem := var_S (var_S var_0) : var env1 IMEM). 
set (dmem := var_S (var_S (var_S var_0)) : var env1 DMEM). 
set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_LOADPC (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 

refine ([| Eset _ (! (var_lift  pc )+ {< Cword 1>})%expr , [!rd <- ! (var_lift pc)] , • , • |])%expr2. 
Defined. 

(* (pc,rf,imem,dmem) where ADD(rd,r1,r2) = imem[pc]
     –> (pc+1, rf[rd <- rf[r1] + rf[r2]], imem, dmem) *)
Definition add_rule : rule state. 
set (env1 := state). 
set (env2 := List.app state  [Treg reg; Treg reg; Treg reg]). 
set (pc := var_0 : var env1 PC). 
set (rf := var_S var_0 : var env1 RF). 
set (imem := var_S (var_S var_0) : var env1 IMEM). 
set (dmem := var_S (var_S (var_S var_0)) : var env1 DMEM). 
set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (r1 := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 
set (r2 := var_S (var_S (var_S (var_S (var_S (var_S var_0))))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_ADD (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 

refine ([| Eset _ (! (var_lift  pc )+ {< Cword 1>})%expr , 
           ([!rd <- (var_lift rf)[? !r1]  + (var_lift rf)[? !r2] ])%expr 
               , • , • |])%expr2. 
Defined. 


(* (pc,rf,imem,dmem) where BZ(rc,ra) = imem[pc] 
     –> (rf[ra], rf , imem, dmem) when rf[rc] = 0 *)
Definition bztaken_rule : rule state. 
set (env1 := state). 
set (env2 := List.app state  [Treg reg; Treg reg]). 
set (pc := var_0 : var env1 PC). 
set (rf := var_S var_0 : var env1 RF). 
set (imem := var_S (var_S var_0) : var env1 IMEM). 
set (dmem := var_S (var_S (var_S var_0)) : var env1 DMEM). 
set (rc := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (ra := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_BZ (imem[? !pc])%expr) . 

apply ( (var_lift rf) [? !rc] =  {< Cword 0 >})%expr. 

refine ([| Eset _ ((var_lift rf)[? !ra])%expr, 
           •
           , • , • |])%expr2. 
Defined. 

(* (pc,rf,imem,dmem) where BZ(rc,ra) = imem[pc] 
     –> (pc+1, rf, imem, dmem) when rf[rc] <> 0 *)
Definition bznottaken_rule : rule state. 
set (env1 := state). 
set (env2 := List.app state  [Treg reg; Treg reg]). 
set (pc := var_0 : var env1 PC). 
set (rf := var_S var_0 : var env1 RF). 
set (imem := var_S (var_S var_0) : var env1 IMEM). 
set (dmem := var_S (var_S (var_S var_0)) : var env1 DMEM). 
set (rc := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (ra := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_BZ (imem[? !pc])%expr) . 

apply ( (var_lift rf) [? !rc] <>  {< Cword 0 >})%expr. 

refine ([| Eset _ (! (var_lift  pc )+ {< Cword 1>})%expr , 
               •
               , • , • |])%expr2. 
Defined. 

(* (pc,rf,imem,dmem) where LOAD(rd,ra) = imem[pc] 
     –> (pc+1, rf[rd := dmem[rf [ra ]]], imem, dmem) *)
Definition load_rule : rule state. 
set (env1 := state). 
set (env2 := List.app state  [Treg reg; Treg reg]). 
set (pc := var_0 : var env1 PC). 
set (rf := var_S var_0 : var env1 RF). 
set (imem := var_S (var_S var_0) : var env1 IMEM). 
set (dmem := var_S (var_S (var_S var_0)) : var env1 DMEM). 
set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (ra := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_LOAD (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 

refine ([|Eset _ (! (var_lift  pc )+ {< Cword 1>})%expr ,
          [ !rd <- (var_lift dmem)[? (!ra)%expr] ]
          , • , • |])%expr2. 
Defined. 

(* (pc,rf,imem,dmem) where STORE(ra,r) = imem[pc] 
     –> (pc+1, rf, imem, dmem[rf[ra] := rf[r]]) *)
Definition store_rule : rule state. 
set (env1 := state). 
set (env2 := List.app state  [Treg reg; Treg reg]). 
set (pc := var_0 : var env1 PC). 
set (rf := var_S var_0 : var env1 RF). 
set (imem := var_S (var_S var_0) : var env1 IMEM). 
set (dmem := var_S (var_S (var_S var_0)) : var env1 DMEM). 
set (ra := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (r := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_STORE (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 

refine ([|Eset _ (! (var_lift  pc )+ {< Cword 1>})%expr ,
          •,
          • , [(var_lift rf)[? (!ra)%expr] <- (var_lift rf) [?(!r)%expr]] |])%expr2. 
Defined. 


Definition TRS : TRS :=
  {| trs_type := state; 
     trs_rules := [ 
                 loadi_rule;
                 loadpc_rule;
                 add_rule;
                 bztaken_rule;
                 bznottaken_rule;
                 load_rule;
                 store_rule
               ]|}. 

Definition init : eval_env eval_type2 state.
unfold eval_env. red. 
split. simpl. apply (Word.repr _ 0). 
split. simpl. apply Regfile.empty. apply (Word.repr _ 0).
split. simpl eval_env. compute. 
Definition AA : Word.T 32 := Word.repr 32 31. 
Definition BB : Word.T 32 := Word.repr 32 3. 
Admitted.     

