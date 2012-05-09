Require Import Common Core. 
Section t. 
  Variable n : nat. 
  Notation OPCODE := (Tlift (Tint 3)). 
  Notation REG := (Tlift (Tint 2)). 
  Notation CONST := (Tlift (Tint n)). 
  
  
  Definition INSTR := Ttuple (OPCODE :: REG :: REG :: REG :: CONST :: nil). 
  
  Notation "[2^n]" := (128). 
  Definition Phi : state := Treg CONST :: Tregfile 4 CONST  :: Tregfile [2^n] INSTR :: Tregfile [2^n] CONST :: nil. 
  
  Ltac set_env := 
    set (PC := var_0 : var Phi (Treg CONST));
    set (RF := var_S (var_0) : var Phi (Tregfile 4 CONST));
    set (IMEM := var_S (var_S (var_0)) : var Phi (Tregfile [2^n] INSTR));
    set (DMEM := var_S (var_S (var_S (var_0))) : var Phi (Tregfile [2^n] CONST)). 
  
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
  
  (* (pc,rf,imem,dmem) where LOADI(rd,const) = imem[pc]
     –> (pc+1, rf[rd <- const], imem, dmem) *)
  Definition loadi_rule  : Action Phi Unit.  intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          WHEN (opcode (!I) =  (#i 0) ) ; 
          DO _ <- (write [: PC <-  (!PC' + #i 1)]);  
          DO _ <- (write RF [: rd (!I) <- const (!I) ]);
          RETURN (#Ctt)). 
  Defined. 
  
  (* (pc,rf,imem,dmem) where LOADPC(rd) = imem[pc]
     –> (pc+1, rf[rd <- pc], imem, dmem) *)
  Definition loadpc_rule : Action Phi Unit.   intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          WHEN (opcode (!I) =  (#i 1) ) ; 
          DO _ <- (write [: PC <-  (!PC' + #i 1)]);  
          DO _ <- (write RF [: rd (!I) <- (!PC') ]);
          RETURN (#Ctt)). 
  Defined.
  
  (* (pc,rf,imem,dmem) where ADD(rd,r1,r2) = imem[pc]
     –> (pc+1, rf[rd <- rf[r1] + rf[r2]], imem, dmem) *)
  Definition add_rule : Action Phi Unit.   intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          WHEN (opcode (!I) =  (#i 2) ) ; 
          DO _ <- (write [: PC <-  (!PC' + #i 1)]);
          DO R1 <- read RF [: r1 (!I) ];
          DO R2 <- read RF [: r2 (!I) ];
          DO _ <- (write RF [: rd (!I) <- (!R1 + !R2) ]);
          RETURN (#Ctt)). 
  Defined. 
  
  (* (pc,rf,imem,dmem) where BZ(r1,r2) = imem[pc] 
     –> (rf[r2], rf , imem, dmem) when rf[r1] = 0 *)
  Definition bztaken_rule : Action Phi Unit. intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          WHEN (opcode (!I) =  (#i 3) );
          DO R1 <- read RF [: r1 (!I) ];
          DO R2 <- read RF [: r2 (!I) ];
          WHEN ( !R1 = #i 0 ); 
          DO _ <- (write [: PC <-  (!R2)]);
          RETURN (#Ctt)). 
  Defined. 
  
  (* (pc,rf,imem,dmem) where BZ(r1,r2) = imem[pc] 
     –> (pc+1, rf , imem, dmem) when rf[r1] <> 0 *)
  Definition bznottaken_rule : Action Phi Unit. intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          WHEN (opcode (!I) =  (#i 3) );
          DO R1 <- read RF [: r1 (!I) ];
          DO R2 <- read RF [: r2 (!I) ];
          WHEN ( !R1 <> #i 0 ); 
          DO _ <- (write [: PC <-  (!PC' + #i 1)]);
          RETURN (#Ctt)). 
  Defined. 
  
  (* (pc,rf,imem,dmem) where LOAD(r1,r2) = imem[pc] 
     –> (pc+1, rf[r1 := dmem[rf [r2 ]]], imem, dmem) *)
  Definition load_rule : Action Phi Unit. intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          WHEN (opcode (!I) =  (#i 4) );
          DO R2 <- read RF [: r2 (!I) ];
          DO D <- read DMEM [: (!R2)];
          DO _ <- (write RF [: r1 (!I) <-  (!D)]);
          DO _ <- (write [: PC <-  (!PC' + #i 1)]);
          RETURN (#Ctt)). 
  Defined. 

  (* (pc,rf,imem,dmem) where STORE(r1,r2) = imem[pc] 
     –> (pc+1, rf, imem, dmem (rf[r1] := rf[r2])) *)
  Definition store_rule : Action Phi Unit. intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          WHEN (opcode (!I) =  (#i 5) );
          DO R1 <- read RF [: r1 (!I) ];
          DO R2 <- read RF [: r2 (!I) ];
          DO _ <- (write DMEM [: (!R1) <-  (!R2)]);
          DO _ <- (write [: PC <-  (!PC' + #i 1)]);
          RETURN (#Ctt)). 
  Defined. 
  
  Definition T : TRS := mk_TRS Phi 
                               (loadi_rule ::
                                           loadpc_rule ::
                                           add_rule ::
                                           bztaken_rule ::
                                           bznottaken_rule ::
                                           load_rule ::
                                           store_rule :: nil). 
End t. 
