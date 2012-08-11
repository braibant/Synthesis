Require Import Common. 
Require (* TaggedUnions *) Core. 
(*
Module Ex1. 
  Section t. 
  Import TaggedUnions. 
  Variable n : nat. 
  Notation OPCODE := (Tlift (Tint 3)). 
  Notation REG := (Tlift (Tint 2)). 
  Notation CONST := (Tlift (Tint n)). 
  
  Open Scope list_scope. 
  Definition INSTR := 
    Tunion 
      (
        [
          Ttuple [REG; CONST];        (* LOADI *) 
          REG;                        (* LOADPC *)
          Ttuple [REG; REG; REG];     (* ADD*)
          Ttuple [REG; REG];          (* BZ *)
          Ttuple [REG; REG];          (* LOAD *)
          Ttuple [REG; REG]           (* STORE *)
        ]
      ). 
  Notation LOADI := (var_0 : var (constrs INSTR) _). 
  Notation LOADPC := (var_S var_0 : var (constrs INSTR) _). 
  Notation ADD := (var_S (var_S var_0) : var (constrs INSTR) _). 
  Notation BZ := (var_S (var_S (var_S var_0)) : var (constrs INSTR) _). 
  Notation LOAD := (var_S (var_S (var_S (var_S var_0))) : var (constrs INSTR) _). 
  Notation STORE := (var_S (var_S (var_S (var_S (var_S var_0)))) : var (constrs INSTR) _). 
  
  Notation "[2^n]" := (128). 
  Definition Phi : state := Treg CONST :: Tregfile 4 CONST  :: Tregfile [2^n] INSTR :: Tregfile [2^n] CONST :: nil. 
  
  Ltac set_env := 
    set (PC := var_0 : var Phi (Treg CONST));
    set (RF := var_S (var_0) : var Phi (Tregfile 4 CONST));
    set (IMEM := var_S (var_S (var_0)) : var Phi (Tregfile [2^n] INSTR));
    set (DMEM := var_S (var_S (var_S (var_0))) : var Phi (Tregfile [2^n] CONST)). 
  
  (* (pc,rf,imem,dmem) where LOADI(rd,const) = imem[pc]
     –> (pc+1, rf[rd <- const], imem, dmem) *)
  Definition loadi_rule  : Action Phi Unit.  intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          MATCH (!I) IN INSTR WITH LOADI OF  rd, const ==> 
            (
              DO _ <- (write [: PC <-  (!PC' + #i 1)]);  
              DO _ <- (write RF [: !rd <- !const ]);
              RETURN (#Ctt))). 
    Defined. 
  
  (* (pc,rf,imem,dmem) where LOADPC(rd) = imem[pc]
     –> (pc+1, rf[rd <- pc], imem, dmem) *)
  Definition loadpc_rule  : Action Phi Unit.  intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          MATCH (!I) IN INSTR WITH LOADPC OF rd ==> 
                (
                  DO _ <- (write [: PC <-  (!PC' + #i 1)]);  
                  DO _ <- (write RF [: !rd <- !PC' ]);
                  RETURN (#Ctt))). 
  Defined. 
  
  (* (pc,rf,imem,dmem) where ADD(rd,r1,r2) = imem[pc]
     –> (pc+1, rf[rd <- rf[r1] + rf[r2]], imem, dmem) *)
  Definition add_rule : Action Phi Unit.   intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          MATCH !I IN INSTR WITH ADD OF  rd , r1 , r2  ==>
            DO _ <- (write [: PC <-  (!PC' + #i 1)]);
            DO R1 <- read RF [: !r1 ];
            DO R2 <- read RF [: !r2 ];
            DO _ <- (write RF [: !rd <- (!R1 + !R2) ]);
            RETURN (#Ctt)). 
  Defined. 
  
  (* (pc,rf,imem,dmem) where BZ(r1,r2) = imem[pc] 
     –> (rf[r2], rf , imem, dmem) when rf[r1] = 0 *)
  Definition bztaken_rule : Action Phi Unit. intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          MATCH !I IN INSTR WITH BZ OF r1 , r2 ==>
          (DO R1 <- read RF [: !r1  ];
           DO R2 <- read RF [: !r2  ];
           WHEN ( !R1 = #i 0 ); 
           DO _ <- (write [: PC <-  (!R2)]);
           RETURN (#Ctt))). 
  Defined. 
  
  (* (pc,rf,imem,dmem) where BZ(r1,r2) = imem[pc] 
     –> (pc+1, rf , imem, dmem) when rf[r1] <> 0 *)
  Definition bznottaken_rule : Action Phi Unit. intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          MATCH !I IN INSTR WITH BZ OF r1 , r2 ==>
          (DO R1 <- read RF [: !r1  ];
           DO R2 <- read RF [: !r2  ];
           WHEN ( !R1 <> #i 0 ); 
           DO _ <- (write [: PC <-  (!PC' + #i 1)]);
           RETURN (#Ctt))). 
  Defined. 
  
  (* (pc,rf,imem,dmem) where LOAD(r1,r2) = imem[pc] 
     –> (pc+1, rf[r1 := dmem[rf [r2 ]]], imem, dmem) *)
  Definition load_rule : Action Phi Unit. intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          MATCH !I IN INSTR WITH LOAD OF r1 , r2 ==>
          DO R2 <- read RF [: !r2  ];
          DO D <- read DMEM [: (!R2)];
          DO _ <- (write RF [: !r1  <-  (!D)]);
          DO _ <- (write [: PC <-  (!PC' + #i 1)]);
          RETURN (#Ctt)). 
  Defined. 

  (* (pc,rf,imem,dmem) where STORE(r1,r2) = imem[pc] 
     –> (pc+1, rf, imem, dmem (rf[r1] := rf[r2])) *)
  Definition store_rule : Action Phi Unit. intros V; set_env. 
  refine (DO PC' <- read [: PC ]; 
          DO I <- read IMEM [: (! PC') ]; 
          MATCH !I IN INSTR WITH STORE OF r1 , r2 ==>
          DO R1 <- read RF [: !r1 ];
          DO R2 <- read RF [: !r2 ];
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
End Ex1. 
*)

Open Scope Z_scope. 
Module Ex2. 
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
       refine (DO PC' <- read [: PC ]; 
               DO I <- read IMEM [: (! PC') ]; 
               WHEN (opcode (!I) =  (#i 0) ) ; 
               DO _ <- (write [: PC <-  (!PC' + #i 1)]);  
               DO _ <- (write RF [: rd (!I) <- const (!I) ]);
               RETURN (#Ctt)). 
      Defined. 
  
  (* (pc,rf,imem,dmem) where LOADPC(rd) = imem[pc]
     –> (pc+1, rf[rd <- pc], imem, dmem) *)
      Definition loadpc_rule : action Phi V Tunit. 
      refine (DO PC' <- read [: PC ]; 
              DO I <- read IMEM [: (! PC') ]; 
              WHEN (opcode (!I) =  (#i 1) ) ; 
              DO _ <- (write [: PC <-  (!PC' + #i 1)]);  
              DO _ <- (write RF [: rd (!I) <- (!PC') ]);
              RETURN (#Ctt)). 
      Defined.
      
      (* (pc,rf,imem,dmem) where ADD(rd,r1,r2) = imem[pc]
     –> (pc+1, rf[rd <- rf[r1] + rf[r2]], imem, dmem) *)
      Definition add_rule : action Phi V Tunit.
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
      Definition bztaken_rule : action Phi V Tunit. 
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
      Definition bznottaken_rule : action Phi V Tunit.
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
      Definition load_rule : action Phi V Tunit. 
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
      Definition store_rule : action Phi V Tunit. 
      refine (DO PC' <- read [: PC ]; 
              DO I <- read IMEM [: (! PC') ]; 
              WHEN (opcode (!I) =  (#i 5) );
              DO R1 <- read RF [: r1 (!I) ];
              DO R2 <- read RF [: r2 (!I) ];
              DO _ <- (write DMEM [: (!R1) <-  (!R2)]);
              DO _ <- (write [: PC <-  (!PC' + #i 1)]);
              RETURN (#Ctt)). 
      Defined. 
    
    Notation "x + y" := (OrElse _ _ _ x y). 
    Definition code :=
      loadi_rule + loadpc_rule + add_rule + bztaken_rule + bznottaken_rule +
                 load_rule + store_rule . 
    End code. 
    Definition Code := fun V => code V.  
  End t. 
End Ex2. 

Require Compiler. 
Require Import FirstOrder Core. 

Eval vm_compute in 
     let x := Compiler.Fo_compile _ _ (Ex2.Code 4) in 
       List.length (FirstOrder.bindings _ _ x). 

Eval vm_compute in 
     let x := Compiler.Fo_CP_compile _ _ (Ex2.Code 4) in 
       List.length (FirstOrder.bindings _ _ x). 

Eval vm_compute in
      Compiler.Fo_compile _ _ (Ex2.Code 4).


(* Definition finish {Phi t} x := List.length (FirstOrder.bindings Phi t(FirstOrder.compile _ _ x)).  *)
(* Eval vm_compute in finish (Compiler.Compile _ _ (Ex2.Code 4) _).  *)
(* Definition step {Phi t} x :=  (CSE.Compile Phi t  (CP.Compile _ _ x)).  *)
(* Eval vm_compute in finish (step (Compiler.Compile _ _ (Ex2.Code 4) ) _).  *)
(* Eval vm_compute in finish (step (step (Compiler.Compile _ _ (Ex2.Code 4) )) _).  *)
(* Eval vm_compute in finish (step (step (step (Compiler.Compile _ _ (Ex2.Code 4) ))) _).  *)



