Require Import Common. 
Open Scope Z_scope. 

Require Import Core Front. 

(** 

In this file, we define a hardware implementation of a small subset of
the Java Virtual Machine. We take the following conventions: 

- the size of the code, the size of the stack, and the number of
registers are the same. 

- the state of the machine is defined by a program counter, that
  denotes the position in the code; a stack pointer, that denotes the
  first free element above the stack; and a set of registers. 

*)

Section t. 
  Variable size : nat.
  (* We use the following ocaml type as a reference, and give assign
  opcodes to instructions accordingly

  type instr = 
  | Iconst of int 			(* push integer on stack *)
  | Ivar   of reg 			(* push register on stack *)
  | Isetvar of reg 			(* pop an integer into a register *)
  | Iadd 					(* pop n2, pop n1, push back n1 + n2 *)
  | Isub 					(* pop n2, pop n1, push back n1 - n2 *)
  | Ibranch_forward of int 		(* move pc to pc + 1 + ofs *)
  | Ibranch_backward of int 		(* move pc to pc + 1 - ofs *)
  | Ibeq of int 				(* pop n2, pop n1, skips ofs forward if n1 = n2 *)
  | Ibne of int 				(* pop n2, pop n1, skips ofs forward if n1 <> n2 *)
  | Ible of int 				(* pop n2, pop n1, skips ofs forward if n1 <= n2 *)
  | Ibgt of int 				(* pop n2, pop n1, skips ofs forward if n1 > n2 *)
  | Ihalt
   *)
  Variable n : nat. 

  Notation OPCODE := (Tint 4).  (* We need 4 bits to encode the opcode *)
  Notation VAL := (Tint n). 

  Open Scope list_scope. 
  Definition INSTR := Ttuple (OPCODE :: VAL :: nil). 
  
  (* type env =
  {
    reg : int array; 
    stack   : int array; 
    mutable sp : int;
    code: instr array;
    mutable pc  : int;     
  }
   *)
  Definition Phi : state := 
    [
      Tregfile n VAL;         (* the registers *)
      Tregfile n VAL;         (* the stack *)
      Treg VAL;                 (* the stack pointer *)
      Tregfile n INSTR;       (* the code *)
      Treg VAL                  (* the program counter *)
    ]. 
  
  Ltac set_env := 
    set (REGS  := var_0 : var Phi (Tregfile n VAL));
    set (STACK := var_S (var_0) : var Phi (Tregfile n VAL));
    set (SP    := var_S (var_S (var_0)) : var Phi (Treg VAL));
    set (CODE  := var_S (var_S (var_S (var_0))) : var Phi (Tregfile n INSTR));
    set (PC    := var_S (var_S (var_S (var_S (var_0)))) : var Phi (Treg VAL)).
    
  Definition opcode {V} (I : expr V INSTR) : expr V OPCODE. 
    eapply Enth. 2: apply I. apply var_0.  
  Defined. 
  
  Definition val {V} (I : expr V INSTR) : expr V VAL. 
    eapply Enth. 2: apply I. apply var_S. apply var_0. 
  Defined. 
  
  Open Scope action_scope. 
  Notation "x \oplus y" := (OrElse _ _ _ x y) (at level 50, left associativity). 

  Section code. 
    (* We parametrise the following code by the variable parameter of the PHOAS representation.   *)
    Variable V : type -> Type. 
   
    Let REGS  := var_0 : var Phi (Tregfile n VAL).
    Let STACK := var_S (var_0) : var Phi (Tregfile n VAL).
    Let SP    := var_S (var_S (var_0)) : var Phi (Treg VAL). 
    Let CODE  := var_S (var_S (var_S (var_0))) : var Phi (Tregfile n INSTR).
    Let PC    := var_S (var_S (var_S (var_S (var_0)))) : var Phi (Treg VAL).
   
    Definition push i : action Phi V Tunit :=
      (do sp <- ! SP;       
       do _ <- write STACK [: sp <- i];             
       do _ <- SP ::= sp + #i 1;
       ret (#Ctt))%action.

    Definition pop : action Phi V VAL :=
      do sp <- ! SP;       
      do x <- read STACK [: sp - #i 1];
      do _ <- SP ::= sp - #i 1;
      ret x. 

 
    Definition Iconst : action Phi V Tunit := (
      do pc <- ! PC; 
      do i <- read CODE [: pc ]; 
      WHEN (opcode i = (#i 0)); 
      do _ <- push (val i);
      PC ::= pc + #i 1              
    )%action.

    Definition Ivar : action Phi V Tunit := 
      (
        do pc <- ! PC; 
        do i <- read CODE [: pc ]; 
        WHEN (opcode i = (#i 1)); 
        do r <- read REGS [: val i];
        do _ <- push r;
        PC ::= pc + #i 1              
      )%action.
    
    Definition Isetvar : action Phi V Tunit := 
      (
        do pc <- ! PC; 
        do i <- read CODE [: pc ]; 
        WHEN (opcode i = (#i 2)); 
        do v <- pop; 
        do _ <- write REGS [: val i <- v];
        PC ::= pc + #i 1              
      )%action.
     
      Definition Iadd : action Phi V Tunit := 
      (
        do pc <- ! PC; 
        do i <- read CODE [: pc ]; 
        WHEN (opcode i = (#i 3)); 
        do sp <- ! SP;       
        do n2 <- read STACK [: sp - #i 1];
        do n1 <- read STACK [: sp - #i 2];
        do _ <- write STACK [: sp - #i 2 <- n1 + n2];                 
        do _ <- SP ::= sp - #i 1;
        PC ::= pc + #i 1              
      )%action.
      
      Definition Isub : action Phi V Tunit := 
      (
        do pc <- ! PC; 
        do i <- read CODE [: pc ]; 
        WHEN (opcode i = (#i 4)); 
        do sp <- ! SP;       
        do n2 <- read STACK [: sp - #i 1];
        do n1 <- read STACK [: sp - #i 2];
        do _ <- write STACK [: sp - #i 2 <- n1 - n2];                 
        do _ <- SP ::= sp - #i 1;
        PC ::= pc + #i 1              
      )%action.
      
      Definition Ibranch_forward : action Phi V Tunit := 
      (
        do pc <- ! PC; 
        do i <- read CODE [: pc ]; 
        WHEN (opcode i = (#i 5)); 
        PC ::= pc + #i 1 + (val i)              
      )%action.

      Definition Ibranch_backward : action Phi V Tunit := 
      (
        do pc <- ! PC; 
        do i <- read CODE [: pc ]; 
        WHEN (opcode i = (#i 6)); 
        PC ::= pc + #i 1 - (val i)              
      )%action.      
      
      Definition Ibranch_cond code cond : action Phi V Tunit := 
        (
          do pc <- ! PC; 
          do i <- read CODE [: pc ]; 
          WHEN (opcode i = (#i code)); 
          do sp <- ! SP;       
          do n2 <- read STACK [: sp - #i 1];
          do n1 <- read STACK [: sp - #i 2];
          do _ <- SP ::= sp - #i 2;
          ((WHEN (cond n1 n2); 
            PC ::= pc + #i 1 + (val i))
             \oplus (PC ::= pc + #i 1))
      )%action.      

      Definition Ibeq: action Phi V Tunit := 
        Ibranch_cond 7 (fun n1 n2 => n1 = n2)%expr. 

      Definition Ibne: action Phi V Tunit := 
        Ibranch_cond 8 (fun n1 n2 => n1 <> n2)%expr. 
      
      Definition Ible: action Phi V Tunit := 
        Ibranch_cond 9 (fun n1 n2 => n1 <= n2)%expr. 

      Definition Ibgt: action Phi V Tunit := 
        Ibranch_cond 10 (fun n1 n2 => n2 < n1)%expr. 
      
      Definition Ihalt: action Phi V Tbool := 
        do pc <- ! PC; 
        do i <- read CODE [: pc ]; 
        WHEN (opcode i = (#i 11)); 
        ret #b true.
      
      (*
  type instr = 
  | Iconst of int 			(* push integer on stack *)
  | Ivar   of reg 			(* push register on stack *)
  | Isetvar of reg 			(* pop an integer into a register *)
  | Iadd 					(* pop n2, pop n1, push back n1 + n2 *)
  | Isub 					(* pop n2, pop n1, push back n1 - n2 *)
  | Ibranch_forward of int 		(* move pc to pc + 1 + ofs *)
  | Ibranch_backward of int 		(* move pc to pc + 1 - ofs *)
  | Ibeq of int 				(* pop n2, pop n1, skips ofs forward if n1 = n2 *)
  | Ibne of int 				(* pop n2, pop n1, skips ofs forward if n1 <> n2 *)
  | Ible of int 				(* pop n2, pop n1, skips ofs forward if n1 <= n2 *)
  | Ibgt of int 				(* pop n2, pop n1, skips ofs forward if n1 > n2 *)
  | Ihalt

       *)

      Definition code :=
        (do _ <- (Iconst \oplus Ivar \oplus Isetvar \oplus Iadd \oplus Isub \oplus Ibranch_forward \oplus Ibranch_backward \oplus Ibeq \oplus Ible \oplus Ibgt); ret (#b false)) \oplus Ihalt.
  End code. 
  Definition Code := fun V => code V.  
End t. 

Require Compiler. 
Require Import FirstOrder RTL Core. 

Definition t := (Compiler.fesiopt _ _ (Code 8)). 


(* Definition finish {Phi t} x := List.length (FirstOrder.bindings Phi t(FirstOrder.compile _ _ x)).  *)
(* Eval vm_compute in finish (Compiler.Compile _ _ (Ex2.Code 4) _).  *)
(* Definition step {Phi t} x :=  (CSE.Compile Phi t  (CP.Compile _ _ x)).  *)
(* Eval vm_compute in finish (step (Compiler.Compile _ _ (Ex2.Code 4) ) _).  *)
(* Eval vm_compute in finish (step (step (Compiler.Compile _ _ (Ex2.Code 4) )) _).  *)
(* Eval vm_compute in finish (step (step (step (Compiler.Compile _ _ (Ex2.Code 4) ))) _).  *)



