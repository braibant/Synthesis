Require Import Common. 
Require Import TRS. 

Definition val := T01 (Tint 16).

Definition reg :=  T01 (Tint 2).  
Definition RF := Tregfile 4 (val). 
Definition INSTR : type1 := 
  Tunion "INSTR" ("LOADI"  of (Ttuple [reg ;val]) 
                 :: "LOADPC" of (reg) 
                 :: "ADD" of (Ttuple [reg;reg;reg]) 
                 :: "BZ" of (Ttuple [reg;reg])
                 :: "LOAD" of (Ttuple [reg;reg])
                 :: "STORE" of (Ttuple [reg;reg])
                 :: nil ). 

Definition IMEM := Tregfile (128) INSTR. 
Definition DMEM := Tregfile (128) val. 
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
(Eget_regfile _ _ _ M _ key)(at level 0, no associativity) : expr_scope. 

Ltac case_match s :=
let rec tac :=
    match goal with 
        |- pattern1_disjunct _ (cons (?id,?t) ?q) => 
          first [(constr_eq s id; apply pattern1_disjunct_hd) 
                | apply pattern1_disjunct_tl; tac]
                
    end
in 
  apply Punion;
  tac; 
try  match goal with 
  |- pattern1 [?x] (?tv) => apply Pvar1
  | |- pattern1 [?x1 ; ?x2] (Ttuple [?t1 ; ?t2]) => apply ([| Pvar1 _ , Pvar1 _|])%pattern
  | |- pattern1 [?x1 ; ?x2 ; ?x3] (Ttuple [?t1 ; ?t2 ; ?t3]) => apply ([| Pvar1 _ , Pvar1 _ , Pvar1 _|])%pattern
  end. 

Definition IS_LOADI : pattern1 ([Treg reg ; Treg val]) INSTR.  
case_match "LOADI". Defined. 

Definition IS_LOADPC : pattern1 ([Treg reg]) INSTR.  
case_match "LOADPC". Defined. 

Definition IS_ADD : pattern1 ([Treg reg; Treg reg; Treg reg]) INSTR.  
case_match "ADD". Defined. 

Definition IS_BZ : pattern1 ([Treg reg; Treg reg]) INSTR.  
case_match "BZ". Defined. 

Definition IS_LOAD : pattern1 ([Treg reg; Treg reg]) INSTR.  
case_match "LOAD". Defined. 

Definition IS_STORE : pattern1 ([Treg reg; Treg reg]) INSTR.  
case_match "STORE". Defined. 

Section rules. 

Let env1 := state. 
Let pc := var_0 : var env1 PC. 
Let rf := var_S var_0 : var env1 RF. 
Let imem := var_S (var_S var_0) : var env1 IMEM. 
Let dmem := var_S (var_S (var_S var_0)) : var env1 DMEM. 

(* (pc,rf,imem,dmem) where LOADI(rd,const) = imem[pc]
     –> (pc+1, rf[rd <- const], imem, dmem) *)
Definition loadi_rule : rule state. 
set (env2 := List.app env1  [Treg reg ; Treg val]). 
set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (const := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg val)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_LOADI (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 
Check (Eset _ _ (! (var_lift  pc )+ {< Cword 1>})%expr). 
apply ([|Eset _ _ (! (var_lift  pc )+ {< Cword 1>})%expr, [(!rd) <- (!const)%expr] ,  • , • |])%expr2.  
Defined. 


(* (pc,rf,imem,dmem) where LOADPC(rd) = imem[pc]
     –> (pc+1, rf[rd <- pc], imem, dmem) *)

Definition loadpc_rule : rule state. 
set (env2 := List.app state  [Treg reg]). 
set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_LOADPC (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 

refine ([| Eset _ _ (! (var_lift  pc )+ {< Cword 1>})%expr , [!rd <- ! (var_lift pc)] , • , • |])%expr2. 
Defined. 

(* (pc,rf,imem,dmem) where ADD(rd,r1,r2) = imem[pc]
     –> (pc+1, rf[rd <- rf[r1] + rf[r2]], imem, dmem) *)
Definition add_rule : rule state. 
set (env2 := List.app state  [Treg reg; Treg reg; Treg reg]). 
set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (r1 := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 
set (r2 := var_S (var_S (var_S (var_S (var_S (var_S var_0))))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_ADD (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 

refine ([| Eset _ _ (! (var_lift  pc )+ {< Cword 1>})%expr , 
           ([!rd <- (var_lift rf)[? !r1]  + (var_lift rf)[? !r2] ])%expr 
               , • , • |])%expr2. 
Defined. 


(* (pc,rf,imem,dmem) where BZ(rc,ra) = imem[pc] 
     –> (rf[ra], rf , imem, dmem) when rf[rc] = 0 *)
Definition bztaken_rule : rule state. 
set (env2 := List.app state  [Treg reg; Treg reg]). 
set (rc := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (ra := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_BZ (imem[? !pc])%expr) . 

apply ( (var_lift rf) [? !rc] =  {< Cword 0 >})%expr. 

refine ([| Eset _ _ ((var_lift rf)[? !ra])%expr, 
           •
           , • , • |])%expr2. 
Defined. 

(* (pc,rf,imem,dmem) where BZ(rc,ra) = imem[pc] 
     –> (pc+1, rf, imem, dmem) when rf[rc] <> 0 *)
Definition bznottaken_rule : rule state. 
set (env2 := List.app state  [Treg reg; Treg reg]). 
set (rc := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (ra := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_BZ (imem[? !pc])%expr) . 

apply ( (var_lift rf) [? !rc] <>  {< Cword 0 >})%expr. 

refine ([| Eset _ _ (! (var_lift  pc )+ {< Cword 1>})%expr , 
               •
               , • , • |])%expr2. 
Defined. 

(* (pc,rf,imem,dmem) where LOAD(rd,ra) = imem[pc] 
     –> (pc+1, rf[rd := dmem[rf [ra ]]], imem, dmem) *)
Definition load_rule : rule state. 
set (env2 := List.app state  [Treg reg; Treg reg]). 
set (rd := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (ra := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_LOAD (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 

refine ([|Eset _ _ (! (var_lift  pc )+ {< Cword 1>})%expr ,
          [ !rd <- (var_lift dmem)[? (!ra)%expr] ]
          , • , • |])%expr2. 
Defined. 

(* (pc,rf,imem,dmem) where STORE(ra,r) = imem[pc] 
     –> (pc+1, rf, imem, dmem[rf[ra] := rf[r]]) *)
Definition store_rule : rule state. 
set (env2 := List.app state  [Treg reg; Treg reg]). 
set (ra := var_S (var_S (var_S (var_S var_0))) : var env2 (Treg reg)). 
set (r := var_S (var_S (var_S (var_S (var_S var_0)))) : var env2 (Treg reg)). 

apply (mk_rule state env1 env2). 
apply trivial_pattern2_vector. 
refine (WHERE IS_STORE (imem[? !pc])%expr) . 

apply ({< Cbool true >})%expr. 

refine ([|Eset _ _  (! (var_lift  pc )+ {< Cword 1>})%expr ,
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

End rules. 

Module Model. 
  Inductive reg : Type := R1 | R2 | R3 | R4. 
  Definition val := Word.T 16. 

  Inductive instr :=
    | loadi  : reg -> val -> instr
    | loadpc : reg -> instr
    | add : reg -> reg -> reg -> instr
    | bz : reg -> reg -> instr
    | load : reg -> reg -> instr
    | store : reg -> reg -> instr. 

  Record state :=
    {
      pc : val;
      rf : reg -> val;
      imem : val -> instr;        (* wrong *)
      dmem : val -> val
    }.
End Model. 


Class relate (X Y : Type) : Type := transform : (X -> Y).  
Notation "X ==> Y" := (relate X Y) (at level 60). 
Instance foo_reg : relate (Model.reg) (eval_type1 reg).  
unfold relate;
refine (fun x => match x with 
                    | Model.R1 => Word.repr _ 0
                    | Model.R2 => Word.repr _ 1
                    | Model.R3 => Word.repr _ 2
                    | Model.R4 => Word.repr _ 3
                end). 
Defined. 

Instance foo_val : relate (Model.val) (eval_type1 val).  
unfold relate. apply id. 
Defined. 

Instance foo_prod2 {A1 A2 B1 B2} 
                   (H1 : relate A1 B1) 
                   (H2 : relate A2 B2) 
  : relate (A1*A2)%type (B1*(B2 * unit ))%type. 
Proof. unfold relate.  intros [x y]. repeat split; auto. Defined.

Instance foo_prod3 {A1 A2 A3 B1 B2 B3} 
                  (H1 : relate A1 B1) 
                  (H2 : relate A2 B2) 
                  (H3 : relate A3 B3) 
  : relate (A1*A2 * A3)%type (B1*(B2 * (B3 * unit)))%type. 
Proof. unfold relate.  intros [[x y] z]. repeat split; auto. Defined.

Instance foo_prod4 {A1 A2 A3 A4 B1 B2 B3 B4} 
                  (H1 : relate A1 B1) 
                  (H2 : relate A2 B2) 
                  (H3 : relate A3 B3) 
                  (H4 : relate A4 B4) 
  : relate (A1*A2 * A3 * A4 )%type (B1*(B2 * (B3 * (B4 * unit))))%type. 
Proof. unfold relate.  intros [[[u x] y] z]. repeat split; auto. Defined.

Instance foo_instr : relate (Model.instr) (eval_type1 INSTR). 
unfold relate.
intros i. refine (match i with 
                    | Model.loadi rd val => inl (transform (rd,val) ) 
                    | Model.loadpc rd => inr (inl (transform rd))
                    | Model.add r1 r2 r3 => inr (inr (inl (transform (r1,r2,r3))))
                    | Model.bz r1 r2 => inr (inr (inr (inl (transform (r1,r2)))))
                    | Model.load r1 r2 => inr (inr (inr (inr (inl (transform (r1,r2))))))
                    | Model.store r1 r2 => inr (inr (inr (inr (inl (transform (r1,r2))))))

                  end 
                 ). 
Defined. 

