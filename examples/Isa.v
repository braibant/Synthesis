Require Import Common. 
Require (* TaggedUnions *) Core. 

Open Scope Z_scope. 
Section t. 
  Require Import Core Front. 
  Variable n : nat. 
  Notation OPCODE := (Tint 3). 
  Notation REG := (Tint 2). 
  Notation CONST := (Tint n). 

  Open Scope list_scope. 
  Definition INSTR := Ttuple (OPCODE :: REG :: REG :: REG :: CONST :: nil). 
  
  Definition Phi : state := Treg CONST :: Tregfile 2 CONST  :: Tregfile n INSTR :: Tregfile n CONST :: nil. 
  
  Ltac set_env := 
    set (PC := var_0 : var Phi (Treg CONST));
    set (RF := var_S (var_0) : var Phi (Tregfile 2 CONST));
    set (IMEM := var_S (var_S (var_0)) : var Phi (Tregfile n INSTR));
    set (DMEM := var_S (var_S (var_S (var_0))) : var Phi (Tregfile n CONST)). 
  
  Ltac fvar n := 
    match n with 
      | 0 => apply var_0
      | S n => apply var_S; fvar n 
    end.
  
  Definition opcode {V} (I : expr V INSTR) : expr V OPCODE. 
  eapply Enth. 2: apply I. fvar 0. 
  Defined. 
  
  Definition rd {V} (I : expr V INSTR) : expr V REG. 
  eapply Enth. 2: apply I. apply var_S. apply var_0. 
  Defined. 
  
  
  Definition r1 {V} (I : expr V INSTR) : expr V REG. 
  eapply Enth. 2: apply I. apply var_S. apply var_S.  apply var_0. 
  Defined. 
  
  Definition r2 {V} (I : expr V INSTR) : expr V REG. 
  eapply Enth. 2: apply I. apply var_S. apply var_S. apply var_S.  apply var_0. 
  Defined. 
  
  Definition const {V} (I : expr V INSTR) : expr V CONST. 
  eapply Enth. 2: apply I. apply var_S. apply var_S. apply var_S. apply var_S. apply var_0. 
    Defined. 
    Open Scope action_scope. 
  (* (pc,rf,imem,dmem) where LOADI(rd,const) = imem[pc]
     –> (pc+1, rf[rd <- const], imem, dmem) *)
    Section code. 
      Variable V : type -> Type. 
       Let PC := var_0 : var Phi (Treg CONST). 
       Let RF := var_S (var_0) : var Phi (Tregfile 2 CONST). 
       Let IMEM := var_S (var_S (var_0)) : var Phi (Tregfile n INSTR). 
       Let DMEM := var_S (var_S (var_S (var_0))) : var Phi (Tregfile n CONST). 
       
       Definition loadi_rule  : action Phi V Tunit. 
       refine (do PC' <- ! PC; 
               do I <- read IMEM [: PC' ]; 
               WHEN (opcode (I) = (#i 0) ) ; 
               PC ::= PC' + #i 1;;
               (write RF [: rd (I) <- const (I) ]);;
               ret (#Ctt))%action. 
      Defined. 
  
  (* (pc,rf,imem,dmem) where LOADPC(rd) = imem[pc]
     –> (pc+1, rf[rd <- pc], imem, dmem) *)
      Definition loadpc_rule : action Phi V Tunit. 
      refine (do PC' <- ! PC ; 
              do I <- read IMEM [: PC' ]; 
              WHEN (opcode (I) =  (#i 1) ) ; 
              PC ::= PC' + #i 1;;
              write RF [: rd (I) <- (PC') ];;
              ret (#Ctt)). 
      Defined.
      
      (* (pc,rf,imem,dmem) where ADD(rd,r1,r2) = imem[pc]
     –> (pc+1, rf[rd <- rf[r1] + rf[r2]], imem, dmem) *)
      Definition add_rule : action Phi V Tunit.
      refine (do PC' <- ! PC; 
              do I <- read IMEM [: PC' ]; 
              WHEN (opcode (I) =  (#i 2) ) ; 
              write [: PC <-  (PC' + #i 1)];;
              do R1 <- read RF [: r1 (I) ];
              do R2 <- read RF [: r2 (I) ];
              do _ <- (write RF [: rd (I) <- (R1 + R2) ]);
              ret (#Ctt)). 
      Defined. 
      
      (* (pc,rf,imem,dmem) where BZ(r1,r2) = imem[pc] 
     –> (rf[r2], rf , imem, dmem) when rf[r1] = 0 *)
      Definition bztaken_rule : action Phi V Tunit. 
      refine (do PC' <- read [: PC ]; 
              do I <- read IMEM [: ( PC') ]; 
              WHEN (opcode (I) =  (#i 3) );
              do R1 <- read RF [: r1 (I) ];
              do R2 <- read RF [: r2 (I) ];
              WHEN ( R1 = #i 0 ); 
              do _ <- (write [: PC <-  (R2)]);
              ret (#Ctt)). 
      Defined. 
      
      (* (pc,rf,imem,dmem) where BZ(r1,r2) = imem[pc] 
     –> (pc+1, rf , imem, dmem) when rf[r1] <> 0 *)
      Definition bznottaken_rule : action Phi V Tunit.
      refine (do PC' <- read [: PC ]; 
              do I <- read IMEM [: ( PC') ]; 
              WHEN (opcode (I) =  (#i 3) );
              do R1 <- read RF [: r1 (I) ];
              do R2 <- read RF [: r2 (I) ];
              WHEN ( R1 <> #i 0 ); 
              do _ <- (write [: PC <-  (PC' + #i 1)]);
              ret (#Ctt)). 
      Defined. 
      
      (* (pc,rf,imem,dmem) where LOAD(r1,r2) = imem[pc] 
     –> (pc+1, rf[r1 := dmem[rf [r2 ]]], imem, dmem) *)
      Definition load_rule : action Phi V Tunit. 
      refine (do PC' <- read [: PC ]; 
              do I <- read IMEM [: ( PC') ]; 
              WHEN (opcode (I) =  (#i 4) );
              do R2 <- read RF [: r2 (I) ];
              do D <- read DMEM [: (R2)];
              write RF [: r1 (I) <-  (D)];;
              PC ::= PC' + #i 1;;
              ret (#Ctt)). 
      Defined. 
      
      (* (pc,rf,imem,dmem) where STORE(r1,r2) = imem[pc] 
     –> (pc+1, rf, imem, dmem (rf[r1] := rf[r2])) *)
      Definition store_rule : action Phi V Tunit. 
      refine (do PC' <- ! PC; 
              do I <- read IMEM [: PC' ]; 
              WHEN (opcode (I) =  (#i 5) );
              do R1 <- read RF [: r1 I ];
              do R2 <- read RF [: r2 I ];
              write DMEM [: R1 <-  R2];;
              PC ::= PC' + #i 1;;
              ret (#Ctt)). 
      Defined. 
    
    Notation "x + y" := (OrElse _ _ _ x y). 
    Definition code :=
      loadi_rule + loadpc_rule + add_rule + bztaken_rule + bznottaken_rule +
                 load_rule + store_rule . 
    End code. 
    Definition Code := fun V => code V.  
End t. 

Require Compiler. 
Require Import FirstOrder RTL Core. 

Definition t := (Compiler.fesiopt _ _ (Code 4)). 

Eval vm_compute in t. 


(* Definition finish {Phi t} x := List.length (FirstOrder.bindings Phi t(FirstOrder.compile _ _ x)).  *)
(* Eval vm_compute in finish (Compiler.Compile _ _ (Ex2.Code 4) _).  *)
(* Definition step {Phi t} x :=  (CSE.Compile Phi t  (CP.Compile _ _ x)).  *)
(* Eval vm_compute in finish (step (Compiler.Compile _ _ (Ex2.Code 4) ) _).  *)
(* Eval vm_compute in finish (step (step (Compiler.Compile _ _ (Ex2.Code 4) )) _).  *)
(* Eval vm_compute in finish (step (step (step (Compiler.Compile _ _ (Ex2.Code 4) ))) _).  *)



