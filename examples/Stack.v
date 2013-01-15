Require Import Common Arith Peano. 
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


Definition Next {A} (f : A -> option A) (m : A ):= 
  match f m with 
    | None => m
    | Some m => m
  end. 

Module Spec. 
  (** * Specification of the stack machine 
 
  This module corresponds to our specification of the stack
  machine: it uses natural numbers everywhere, and uses dynamic check
  to map undefined behaviors to the halting state *)

  Notation id := nat. 
  Inductive cond := Ceq | Cne | Cle | Cgt. 
  Inductive instruction: Type :=
  | Iconst(n: nat) 
  | Ivar(x: id)
  | Isetvar(x: id) 
  | Iadd 
  | Isub 
  | Ibranch_forward(ofs: nat)
  | Ibranch_backward(ofs: nat)
  | Ibranch_cond (c : cond) (ofs : nat)
  | Ihalt. 

  
  Definition code := list instruction.

  Fixpoint code_at (C: code) (pc: nat) : option instruction :=
    match C, pc with
      | nil, _ => None
      | i :: C', O => Some i
      | i :: C', S pc' => code_at C' pc'
    end%list.
  
  Definition stack := list nat.
  
  Definition store := id -> nat. 

  Require Import NPeano. 

  Definition update (s:store) (x:id) (v : nat) := 
    fun y => if Nat.eqb x y then v else s y.
  
  Record machine := mk
    {
      c   : code;      
      pc : nat;
      stk : stack;
      str : store
    }.
  
  Require Import List. 
  
  Section t. 
    (** We use a dynamic check to verify that the state we reach is
    valid, and some checks on, e.g., results of arithmetic operations,
    to ensure that we are not outside of the scope of validity of this
    definition. *)
  
    Variable bound : nat.
    Definition dyncheck  (s : machine) :=
      check (Nat.ltb (pc s) bound);
      check (Nat.ltb (List.length (stk s)) bound);
      Some s.

    (** * Next step relation for the stack machine *)
    Definition step (s : machine) : option machine :=
      do op <- code_at (c s) (pc s);
      match op with 
        | Iconst n => 
          check (n <? bound);
          dyncheck (mk (c s) (pc s +1) (n :: stk s) (str s))
        | Ivar x => 
          check (x <? bound);
          dyncheck (mk (c s) (pc s +1) ((str s) x :: stk s) (str s))
        | Isetvar x => 
          check (x <? bound);
          match stk s with
            | nil => None
            | v :: stk => 
              dyncheck (mk (c s) (pc s +1) (stk) (update (str s) x v))
          end
        | Iadd =>
          match stk s with
            | nil => None
            | cons _ nil => None
            | n1 :: n2 :: stk => 
              check (n1 + n2 <? bound);
              dyncheck (mk (c s) (pc s +1) (n1 + n2 :: stk)  (str s) )
          end
        | Isub =>
          match stk s with
            | nil => None
            | cons _ nil => None
            | n2 :: n1 :: stk => 
              check (n2 <=? n1);
              dyncheck (mk (c s) (pc s +1) (n1 - n2 :: stk)  (str s) )
          end
        | Ibranch_forward ofs => 
          dyncheck (mk (c s) (pc s + 1 + ofs) (stk s) (str s))
        | Ibranch_backward ofs => 
          check (ofs <=? pc s + 1);
          dyncheck (mk (c s) (pc s + 1 - ofs) (stk s) (str s))
        | Ibranch_cond test ofs => 
          match stk s with
            | nil => None
            | cons _ nil => None
            | n2 :: n1 :: stk => 
              let t := match test with 
                           | Ceq => NPeano.Nat.eqb n1 n2 
                           | Cne => negb (NPeano.Nat.eqb n1 n2)
                           | Cle => (NPeano.Nat.leb n1 n2)%bool
                           | Cgt => negb ((NPeano.Nat.leb n1 n2 ))%bool
                       end
              in
              if t  
              then
                dyncheck (mk (c s) (pc s +1 + ofs) stk  (str s) )
              else
                dyncheck (mk (c s) (pc s +1) stk  (str s) )
             
          end
        | _ => None
      end.
  End t.

(** We were heavily inspired by the following definition that comes from a course by X. Leroy

  Inductive transition (C: code): machine_state -> machine_state -> Prop :=
  | trans_const: forall pc stk s n,
                   code_at C pc = Some(Iconst n) ->
                   transition C (pc, stk, s) (pc + 1, n :: stk, s)
  | trans_var: forall pc stk s x,
                 code_at C pc = Some(Ivar x) ->
                 transition C (pc, stk, s) (pc + 1, s x :: stk, s)
  | trans_setvar: forall pc stk s x n,
                    code_at C pc = Some(Isetvar x) ->
                    transition C (pc, n :: stk, s) (pc + 1, stk, update s x n)
  | trans_add: forall pc stk s n1 n2,
                 code_at C pc = Some(Iadd) ->
                 transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 + n2) :: stk, s)
  | trans_sub: forall pc stk s n1 n2,
                 code_at C pc = Some(Isub) ->
      transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 - n2) :: stk, s)
  | trans_mul: forall pc stk s n1 n2,
                 code_at C pc = Some(Imul) ->
                 transition C (pc, n2 :: n1 :: stk, s) (pc + 1, (n1 * n2) :: stk, s)

  | trans_branch_forward: forall pc stk s ofs pc',
                            code_at C pc = Some(Ibranch_forward ofs) ->
                            pc' = pc + 1 + ofs ->
                            transition C (pc, stk, s) (pc', stk, s)
  | trans_branch_backward: forall pc stk s ofs pc',
                             code_at C pc = Some(Ibranch_backward ofs) ->
                             pc' = pc + 1 - ofs ->
                             transition C (pc, stk, s) (pc', stk, s)
  | trans_beq: forall pc stk s ofs n1 n2 pc',
                 code_at C pc = Some(Ibeq ofs) ->
                 pc' = (if beq_nat n1 n2 then pc + 1 + ofs else pc + 1) ->
                 transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_bne: forall pc stk s ofs n1 n2 pc',
                 code_at C pc = Some(Ibne ofs) ->
                 pc' = (if beq_nat n1 n2 then pc + 1 else pc + 1 + ofs) ->
                 transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_ble: forall pc stk s ofs n1 n2 pc',
                 code_at C pc = Some(Ible ofs) ->
                 pc' = (if Nat.leb n1 n2 then pc + 1 + ofs else pc + 1) ->
                 transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s)
  | trans_bgt: forall pc stk s ofs n1 n2 pc',
                 code_at C pc = Some(Ibgt ofs) ->
                 pc' = (if Nat.leb n1 n2 then pc + 1 else pc + 1 + ofs) ->
                 transition C (pc, n2 :: n1 :: stk, s) (pc', stk, s).
*)

End Spec. 


Module Circuit. 
Section t. 
  Variable size : nat.
  (** Fe-Si implementation of the Stack machine *)

  (** We use the following ocaml type as a reference, and give assign
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
  Definition Phi : state := 
    [
      Tregfile n INSTR;       (* the code *)
      Treg VAL;                  (* the program counter *)
      Tregfile n VAL;         (* the stack *)
      Treg VAL;                 (* the stack pointer *)
      Tregfile n VAL         (* the registers *)     
    ]. 
      
  Definition opcode {V} (I : expr V INSTR) : expr V OPCODE. 
    eapply Enth. 2: apply I. apply var_0.  
  Defined. 
  
  Definition val {V} (I : expr V INSTR) : expr V VAL. 
    eapply Enth. 2: apply I. apply var_S. apply var_0. 
  Defined. 
  
  Open Scope action_scope. 
  Notation "x \oplus y" := (OrElse _ _ _ x y) (at level 51, right associativity). 

  Section code. 
    (** We parametrise the following code by the variable parameter of the PHOAS representation.   *)
    Variable V : type -> Type. 

    Definition CODE  := (var_0) : var Phi (Tregfile n INSTR).
    Definition PC    := var_S (var_0) : var Phi (Treg VAL).
    Definition STACK := var_S (var_S (var_0)) : var Phi (Tregfile n VAL).
    Definition SP    := var_S (var_S (var_S (var_0))) : var Phi (Treg VAL).
    Definition REGS  := var_S (var_S (var_S (var_S (var_0)))) : var Phi (Tregfile n VAL).
    
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

 
    Definition Iconst  (pc: expr V VAL) (i : expr V INSTR) : action Phi V Tunit :=(
      do _ <- push (val i);
      PC ::= pc + #i 1              
    )%action.
    
    
    Definition Ivar (pc: expr V VAL) (i : expr V INSTR) : action Phi V Tunit := 
      (
        do r <- read REGS [: val i];
        do _ <- push r;
        PC ::= pc + #i 1              
      )%action.
    
    Definition Isetvar (pc: expr V VAL) (i : expr V INSTR) : action Phi V Tunit := 
      (
        do v <- pop; 
        do _ <- write REGS [: val i <- v];
        PC ::= pc + #i 1              
      )%action.
     
      Definition Iadd(pc: expr V VAL) (i : expr V INSTR) : action Phi V Tunit :=
      (
        do sp <- ! SP;       
        do n2 <- read STACK [: sp - #i 1];
        do n1 <- read STACK [: sp - #i 2];
        do _ <- write STACK [: sp - #i 2 <- n1 + n2];                 
        do _ <- SP ::= sp - #i 1;
        PC ::= pc + #i 1              
      )%action.
      
      Definition Isub (pc: expr V VAL) (i : expr V INSTR) : action Phi V Tunit :=
      (
        do sp <- ! SP;       
        do n2 <- read STACK [: sp - #i 1];
        do n1 <- read STACK [: sp - #i 2];
        do _ <- write STACK [: sp - #i 2 <- n1 - n2];                 
        do _ <- SP ::= sp - #i 1;
        PC ::= pc + #i 1              
      )%action.
      
      Definition Ibranch_forward (pc: expr V VAL) (i : expr V INSTR) : action Phi V Tunit :=
      (
        PC ::= pc + #i 1 + (val i)              
      )%action.
      
      
      
      Definition Ibranch_backward (pc: expr V VAL) (i : expr V INSTR) : action Phi V Tunit :=
      (
        PC ::= pc + #i 1 - (val i)              
      )%action.      
      
      Definition Ibranch_cond cond (pc: expr V VAL) (i : expr V INSTR) : action Phi V Tunit :=
        (
          do sp <- ! SP;       
          do n2 <- read STACK [: sp - #i 1];
          do n1 <- read STACK [: sp - #i 2];
          do _ <- SP ::= sp - #i 2;
          ((when (cond n1 n2) do
            PC ::= pc + #i 1 + (val i))
             \oplus (PC ::= pc + #i 1))
      )%action.      

      Definition Ibeq := 
        Ibranch_cond (fun n1 n2 => n1 = n2)%expr. 

      Definition Ibne := 
        Ibranch_cond (fun n1 n2 => n1 <> n2)%expr. 
      
      Definition Ible := 
        Ibranch_cond (fun n1 n2 => n1 <= n2)%expr. 

      Definition Ibgt := 
        Ibranch_cond (fun n1 n2 => n2 < n1)%expr. 
      
      Definition Ihalt (pc: expr V VAL) (i : expr V INSTR) : action Phi V B :=
        when (opcode i = (#i 11)) do
        ret #b true.
      
      Definition code_at {T} f : action Phi V T:=
        do pc <- ! PC;
        do i  <- read CODE [: pc];
        f pc i.
      
      Fixpoint case {S T} (x : expr V S) (l : list (expr V S * action Phi V T)) default :=
        match l with 
          | nil => default
          | (c,a) :: q => 
            (when (x = c) do a) 
              \oplus (when (x <> c) do case x q default)
        end. 

      Require Import ZArith. 
      Definition mk_val {n} v : expr V (Int n) := (#i (Z.of_nat v)).
                              
      Definition code :=
        code_at (fun pc i =>
                   case (opcode i)
                        ([
                            (mk_val 0, Iconst pc i);
                            (mk_val 1, Ivar   pc i);
                            (mk_val 2, Isetvar pc i);
                            (mk_val 3, Iadd pc i);
                            (mk_val 4, Isub pc i);
                            (mk_val 5, Ibranch_forward pc i);
                            (mk_val 6, Ibranch_backward pc i);
                            (mk_val 7, Ibeq pc i);
                            (mk_val 8, Ibne pc i);
                            (mk_val 9, Ible pc i);
                            (mk_val 10, Ibgt pc i)
                        ])
                        ret (# Ctt )) .
  End code. 
  Definition Code := fun V => code V.  
  Definition Next m := Front.Next _ m (Code).
End t.
End Circuit.

Section t. 
  Variable size : nat. 
  Notation n := (Word.power2 size). 

  Notation V := eval_type. 
  
  Definition step  {Phi t} (A : action Phi eval_type t) st : 
    option (eval_state Phi) :=    
    match Sem.eval_action  A st (Diff.init Phi)  with
      | Some p => Some (Diff.apply Phi (snd p) st)
      | None => None
    end. 
  Require Import ZArith DList. 
  Definition mk_val v : eval_type (Int size) := Word.repr size (Z.of_nat v).

  Notation "x =%= y" := (mk_val x = y) (at level 80).
  
  Notation c  m2 := (DList.DList.get (Circuit.CODE size) m2).    
  Notation pc m2 := (DList.DList.get (Circuit.PC size) m2).    
  Notation stk m2 := (DList.DList.get (Circuit.STACK size) m2).
  Notation sp m2 := (DList.DList.get (Circuit.SP size) m2).
  Notation str m2 := (DList.DList.get (Circuit.REGS size) m2).
  (* 
    Definition CODE  := (var_0) : var Phi (Tregfile n INSTR).
    Definition PC    := var_S (var_0) : var Phi (Treg VAL).
    Definition STACK := var_S (var_S (var_0)) : var Phi (Tregfile n VAL).
    Definition SP    := var_S (var_S (var_S (var_0))) : var Phi (Treg VAL).
    Definition REGS  := var_S (var_S (var_S (var_S (var_0)))) : var Phi (Tregfile n VAL).
   *)

  Require Import ZArith. 
  
  Definition cast_instr op val : eval_type (Circuit.INSTR size) :=
    (Word.repr _ (Z.of_nat op), (Word.repr _ (Z.of_nat val) , tt)).
  
  Definition mk_instr (i : Spec.instruction) : eval_type (Circuit.INSTR size) :=
    match i with
      | Spec.Iconst x =>  cast_instr 0 x 
      | Spec.Ivar x =>    cast_instr 1 x
      | Spec.Isetvar x => cast_instr 2 x
      | Spec.Iadd =>      cast_instr 3 0
      | Spec.Isub =>      cast_instr 4 0
      | Spec.Ibranch_forward ofs => cast_instr 5 ofs
      | Spec.Ibranch_backward ofs => cast_instr 6 ofs
      | Spec.Ibranch_cond Spec.Ceq ofs =>             cast_instr 7 ofs
      | Spec.Ibranch_cond Spec.Cne ofs =>             cast_instr 8 ofs
      | Spec.Ibranch_cond Spec.Cle ofs =>             cast_instr 9 ofs
      | Spec.Ibranch_cond Spec.Cgt ofs =>             cast_instr 10 ofs
      | Spec.Ihalt =>                cast_instr 11 0
    end.

  (** The property that states that the code on both machines are compatible  *)
  Definition R_code (m1 : Spec.machine) (m2 : eval_state (Circuit.Phi size)) :  Prop :=
    forall p, p < n -> 
         match Spec.code_at (Spec.c m1) p with 
           | None => False
           | Some i => mk_instr i = Regfile.get (c m2) (mk_val p)
         end.

  (** We define what it means for stacks to be compatible *)
  Definition R_stk l v := 
    forall i i', i < List.length l ->  
         i =%= i' ->
         Regfile.get v i' = mk_val (List.nth i (List.rev l) 0).
  
  Definition R_str st v := 
    forall i i', i < n ->  
            i =%= i' ->
            st i =%= Regfile.get v i'.
    
  (** The invariant that relates the execution of the machines  *)
  Record R (m1 : Spec.machine) (m2 : eval_state (Circuit.Phi size)) :  Prop := 
    {
      Rpc1 : Spec.pc m1 =%= pc m2;
      Rpc2 : Spec.pc m1 < n;
      (* properties about the stack *)
      Rstk : R_stk (Spec.stk m1) (stk m2);
      Rsp1 : List.length (Spec.stk m1) =%= sp m2;
      Rsp2 : List.length (Spec.stk m1) < n;
      Rsp3 : forall x, List.In x (Spec.stk m1) -> x < n;
      (* properties about the store *)
      Rstr1  : R_str (Spec.str m1) (str m2);
      Rstr2  : forall x, Spec.str m1 x < n
    }.

  Hint Resolve Rpc1 Rpc2 Rstk Rsp1 Rsp2 Rsp3 Rstr1 Rstr2. 
  
  Notation "x == y" := (R x y) (at level 80).

  Lemma step_code_at {T} m1 m2 (f : expr V (Int size) -> expr V (Circuit.INSTR size) -> 
                                  action (Circuit.Phi size) V T):          
    R_code m1 m2 ->
    m1 == m2 -> 
    step (Circuit.code_at _ _ f)%action m2
    = do i <- Spec.code_at (Spec.c m1) (Spec.pc m1);
    step (f (Evar (mk_val (Spec.pc m1)))%expr (Evar (mk_instr i))) m2.
  Proof. 
    intros Hcode H.
    unfold Circuit.code_at. 
    unfold step at 1. Opaque DList.DList.get. Opaque Diff.apply.   
    simpl. unfold Sem.Dyn.Bind.
    rewrite (Rpc1 _ _ H).
    refine (let H := Hcode (Spec.pc m1) (Rpc2 _ _ H) in _).     rewrite (Rpc1 _ _ H) in H0.
    destruct (Spec.code_at (Spec.c m1) (Spec.pc m1)) eqn:?. simpl. rewrite H0. reflexivity. 
    tauto. 
  Qed.
  
  Add  Ring wring : (Word.ring size).
    
  Lemma repr_add m x y: Word.repr m (x + y) = Word.add (Word.repr m x) (Word.repr m y).
    apply Word.unsigned_inj. simpl. 
    rewrite Zplus_mod. reflexivity.
  Qed. 

  Lemma repr_sub m (x y : Z) : Word.repr m (x - y) = Word.sub (Word.repr m x) (Word.repr m y).
  Proof.
    apply Word.unsigned_inj; simpl.
    rewrite Zminus_mod. reflexivity. 
  Qed. 

  Lemma Rval_succ : forall x, x + 1 =%= Word.add (mk_val x) (Cword 1%Z).
  Proof. 
    intros. 
    unfold mk_val. rewrite plus_comm. rewrite Nat2Z.inj_succ.   rewrite <- Z.add_1_l. rewrite repr_add. unfold Cword. simpl. ring. 
  Qed. 

  Lemma Rval_add : forall x y, x + y =%= Word.add (mk_val x) (mk_val y).
  Proof. 
    intros. 
    unfold mk_val. rewrite Nat2Z.inj_add. rewrite repr_add. reflexivity. 
  Qed. 

  Lemma Rval_sub : forall x y, y <= x -> x - y =%= Word.sub (mk_val x) (mk_val y%Z).
  Proof.
    intros. 
    unfold mk_val. rewrite Nat2Z.inj_sub by omega. 
    apply repr_sub. 
  Qed. 


  Lemma Rval_add_morphism : forall x1 y1 x2 y2, x1 =%= x2 -> y1 =%= y2 -> x1 + y1 =%= Word.add x2 y2. 
  Proof. 
    intros. rewrite <- H, <- H0. apply Rval_add. 
  Qed. 
  
  Lemma Rval_sub_morphism : forall x1 y1 x2 y2, x1 =%= x2 -> y1 =%= y2 -> 
                                                   y1 <= x1 -> x1 - y1 =%= Word.sub x2 y2. 
  Proof. 
    intros. 
    rewrite <- H, <- H0. 
    apply Rval_sub. omega. 
  Qed. 


  Lemma Rval_length_1 {A} (l: list A) hd tl x: 
    l = hd :: tl ->
    List.length l  =%= x ->
    List.length tl =%= Word.sub x (Cword 1%Z).
  Proof. 
    intros. 
    replace (List.length tl) with (List.length l - 1) by (rewrite H; simpl; try omega).  
    rewrite <- H0. apply Rval_sub_morphism; auto. rewrite H. simpl; omega. 
  Qed. 
  Lemma Rval_length_2 {A} (l: list A) hd1 hd2 tl x: 
    l = hd1 :: hd2 :: tl ->
    List.length l  =%= x ->
    List.length tl =%= Word.sub x (Cword 2%Z).
  Proof. 
    intros. 
    replace (List.length tl) with (List.length l - 2) by (rewrite H; simpl; try omega).  
    rewrite <- H0. apply Rval_sub_morphism; auto. rewrite H. simpl; omega. 
  Qed. 
  
  (** We use the [val] hint db for theorems that deal with the Rval relation *)
  Hint Resolve Rval_succ Rval_add Rval_sub Rval_add_morphism Rval_sub_morphism : val. 
  Hint Resolve Rval_length_1 Rval_length_2 : val. 

  Fixpoint case {A B} (eq : A -> A -> bool) e (l: list (A *B)) default :=
    match l with 
      | nil => default
      | (t,v) :: q => if eq e t then v else case eq e q default
      end.
  
    
  Lemma step_case {S T k} (e: expr V S) l (default : action _ V T) d: 
    step (Circuit.case k V e l default) d =
    step (case (fun x y => type_eq _ (eval_expr _ x) (eval_expr _ y)) e l default) d.
  Proof. 
    induction l. 
    - reflexivity. 
    - simpl. destruct a. 
      destruct (type_eq S (eval_expr S e) (eval_expr S e0)) eqn: He. 
      destruct (step a d) eqn:Ha. 
      + 
      Lemma step_OrElse2 Phi t  A B d:
        step B d = None -> 
        step (OrElse Phi V t A B) d = step A d.
      Proof. 
        unfold step. simpl. intros H. unfold Sem.Dyn.OrElse. 
        destruct (        Sem.eval_action A d (Diff.init Phi)) eqn: HA.
        f_equal. 
        auto. 
      Qed. 
      rewrite step_OrElse2. 
      Lemma step_when_true  Phi t A C d :                
        eval_expr Tbool C = true -> 
        step (when C do A) d = @step Phi t A d.
      Proof. 
        unfold step. simpl. intros H. rewrite H. unfold Sem.Dyn.Bind.  simpl. reflexivity. 
      Qed. 
      
      rewrite step_when_true; simpl;  auto. 
      Lemma step_when_false  Phi t A C d :                
        eval_expr Tbool C = false -> 
        @step Phi t (when C do A) d = None.
      Proof. 
        unfold step. simpl. intros H. rewrite H. unfold Sem.Dyn.Bind.  simpl. reflexivity. 
      Qed. 
      rewrite step_when_false. auto. simpl. rewrite He. reflexivity. 
      
      + rewrite step_OrElse2. rewrite step_when_true. auto. 
        simpl; auto.
        rewrite step_when_false. auto. simpl; rewrite He; auto. 
      + 
        Lemma step_OrElse1 Phi t A B d:
          step A d = None -> 
          step (OrElse Phi V t A B) d = step B d.
        Proof. 
          unfold step. simpl. intros H.  unfold Sem.Dyn.OrElse.       destruct (        Sem.eval_action A d (Diff.init Phi)) eqn: HA. discriminate.  reflexivity. 
        Qed.
        rewrite step_OrElse1.
        rewrite step_when_true. auto. 
        simpl. rewrite Bool.negb_true_iff. auto. 
        rewrite step_when_false. auto. auto. 
  Qed. 
  
  (** pushing elements on the stack preserves the stk part of the invariant *)
  Lemma push_correct_stk stk1 stk2 x1 x2 p: x1 =%= x2 -> 
                                      R_stk stk1 stk2  ->
                                      mk_val (List.length stk1) = p ->
                                      List.length stk1 < n -> 
                                      R_stk (x1 :: stk1) (Regfile.set (stk2) p x2).
  Proof. 
    unfold R_stk; simpl. intros Hx H Hp Hstk i i' Hi  Hi' . rewrite <- Hi'. clear Hi'. 
    assert (Hi' : i < List.length stk1 \/ i = (List.length stk1)) by omega; clear Hi.
    destruct Hi' as [Hi | Hi]. 
    * rewrite Regfile.gso. rewrite List.app_nth1 by (rewrite List.rev_length;auto).      
      apply H;auto. 
      simpl in *. 
      clear - Hstk Hi Hp. rewrite <- Hp. clear Hp. 
      apply (Word.not_eqb size); assumption. 
    * rewrite List.app_nth2 by (rewrite List.rev_length;omega). 
      rewrite Hi. rewrite List.rev_length. rewrite minus_diag. simpl. 
      rewrite Regfile.gss.  auto. 
      simpl in *.  rewrite Hp. 
      
      Lemma Word'eqb_refl : forall n (x: Word.T n), Word.eqb x x = true. 
      Proof. 
        intros. rewrite Word.eqb_correct. reflexivity.
      Qed.
      apply Word'eqb_refl. 
  Qed.  
  
  Hint Extern 4  (_ < _) => rewrite <- NPeano.Nat.ltb_lt. 
  (** pushing elements on the stack preserves the stack pointer part of the invariant  *)
  Lemma push_correct_sp m1 m2 :
    m1 == m2 -> 
    S (Datatypes.length (Spec.stk m1)) =%=
      Word.add (DList.hd (DList.tl (DList.tl (DList.tl m2)))) (Cword 1%Z).
  Proof. 
    destruct 1 as [_ _ _ H].
    Transparent DList.get. simpl in *. Opaque DList.get.
    rewrite <- H. rewrite <- NPeano.Nat.add_1_r. apply Rval_succ.        
  Qed.   
  Hint Resolve push_correct_sp.

  Lemma pop_correct_stk hd tl v : R_stk (hd :: tl) (v) -> 
                                      R_stk (tl) (v).
  Proof.
    unfold R_stk; simpl. intros. 
    rewrite (H i); auto. 
    rewrite List.app_nth1 by (rewrite List.rev_length; omega). reflexivity. 
  Qed.
  
  Lemma pop_correct_sp m1 m2 hd tl k : m1 == m2 -> 
                                     Spec.stk m1 = hd :: tl -> 
                                     k = Datatypes.length tl -> 
                                     k =%= Word.sub (DList.hd (DList.tl (DList.tl (DList.tl m2)))) (Cword 1%Z).
  Proof. 
    intros. unfold Cword. 
    replace k with (List.length (Spec.stk m1) - 1). apply Rval_sub_morphism. 
    destruct H; simpl in *; auto. 
    reflexivity. 
    rewrite H0; simpl; omega. 
    rewrite H0. simpl. omega. 
  Qed.
  
  Hint Resolve pop_correct_sp.


  Lemma pop2_correct_sp m1 m2 hd1 hd2 tl k : m1 == m2 -> 
                                        Spec.stk m1 = hd1 :: hd2 :: tl -> 
                                        k = Datatypes.length tl -> 
                                        k =%= Word.sub (DList.hd (DList.tl (DList.tl (DList.tl m2)))) (Cword 2%Z).
  Proof. 
    intros. unfold Cword. 
    replace k with (List.length (Spec.stk m1) - 2). apply Rval_sub_morphism. 
    destruct H; simpl in *; auto. 
    reflexivity. 
    rewrite H0; simpl; omega. 
    rewrite H0. simpl. omega. 
  Qed.
  
  Hint Resolve pop2_correct_sp.

  Definition branch_cond_eval cond n1 n2 :=
    match cond with
      | Spec.Ceq => NPeano.Nat.eqb n1 n2
      | Spec.Cne => negb (NPeano.Nat.eqb n1 n2)
      | Spec.Cle => NPeano.Nat.leb n1 n2
      | Spec.Cgt => negb (NPeano.Nat.leb n1 n2)
    end.
  
  Require Import Consider. 

  Ltac list_length_tac :=
      repeat 
        match goal with 
            |- context [List.length (List.rev _)] => rewrite List.rev_length
          | |- context [List.length (List.app _ _)] => rewrite List.app_length
          | H : ?l = _ |- context [List.length ?l] => rewrite H
        end; simpl; omega.
  
  Hint Extern 4  (_ < _) => list_length_tac. 
  Hint Extern 4  (_ <= _) => list_length_tac. 
  Hint Extern 4  (_ > _) => list_length_tac. 
  Hint Extern 4  (_ >= _) => list_length_tac. 

  Hint Extern 4 (R_stk _ _) => match goal with 
                                | H : _ == _ |- _ => clear - H; destruct H; simpl in *
                              end. 
  Hint Extern 4 (_ =%= _) =>  match goal with 
                               | H : _ == _ |- _ => clear - H; destruct H; simpl in * end.

  Lemma hint_length m1 m2 x y s: m1 == m2 -> 
                           Spec.stk m1 = x :: y :: s ->                                          
                           Datatypes.length s < n.
  Proof.
    intros. destruct H; simpl in *.  rewrite H0 in Rsp5.  simpl in *. omega. 
  Qed. 
  
  Hint Resolve hint_length. 
  
  Lemma pop2_correct_stk m1 m2 x y s: m1 == m2 -> 
                                      Spec.stk m1 = x :: y :: s -> 
                                      R_stk s  (DList.hd (DList.tl (DList.tl m2))).
  Proof. 
    intros. 
    destruct H. simpl in *. 
    apply (pop_correct_stk y). 
    apply (pop_correct_stk x). 
    rewrite <- H0. apply Rstk0. 
  Qed. 
  Hint Resolve pop2_correct_stk.  
    

          
  Lemma stk_1 m1 m2 a1 s: 
    m1 == m2 -> 
    Spec.stk m1 = a1 :: s -> 
    a1 =%= Regfile.get (stk m2) (Word.sub (sp m2) (Cword 1%Z)) . 
  Proof. 
    intros H Heq.
    destruct H as [Hpc1 Hpc2 Hstk Hsp].
    simpl in *. 
    rewrite (Hstk ((List.length s))); auto.
    rewrite Heq. simpl. 
    rewrite List.app_nth2. rewrite List.rev_length.  rewrite minus_diag. simpl. reflexivity. 
    auto.
    change (Cword 1%Z) with (mk_val 1). rewrite <- Hsp.
    rewrite <- Rval_sub. 
    rewrite Heq. simpl. rewrite <- minus_n_O. reflexivity. rewrite Heq. simpl. omega. 
  Qed. 
  
  Lemma stk_2 m1 m2 a1 a2 s: 
    m1 == m2 -> 
    Spec.stk m1 = a1 :: a2 :: s -> 
    a2 =%= Regfile.get (stk m2) (Word.sub (sp m2) (Cword 2%Z)) . 
  Proof. 
    intros H Heq.
    destruct H as [Hpc1 Hpc2 Hstk Hsp].
    simpl in *. 
    rewrite (Hstk ((List.length s))); auto. 
    rewrite Heq. simpl. 
    rewrite List.app_nth1; auto.  
    rewrite List.app_nth2; auto.
    rewrite List.rev_length.  rewrite minus_diag. simpl. reflexivity.
    rewrite <- Hsp. replace ((List.length s)) with (List.length (Spec.stk m1) - 2). 
    apply Rval_sub. 
    auto.
    rewrite Heq.  simpl.  omega. 
  Qed. 
  
      
  Transparent Diff.apply. Transparent Diff.add. Transparent Diff.init. 
  Transparent DList.get. 

  Lemma Rsp3_pop2 m1 m2 x1 x2 s : 
    m1 == m2 -> 
    Spec.stk m1 = x1 :: x2 :: s -> 
    (forall x, List.In x s -> x < n). 
  Proof. 
    intros. apply (Rsp3 _ _ H).  rewrite H0. simpl.  intuition. 
  Qed.
  Hint Resolve Rsp3_pop2 : stack. 

  Lemma Rsp3_pop1 m1 m2 x1 s : 
    m1 == m2 -> 
    Spec.stk m1 = x1 :: s -> 
    (forall x, List.In x s -> x < n). 
  Proof. 
    intros. apply (Rsp3 _ _ H).  rewrite H0. simpl.  intuition. 
  Qed.
  Hint Resolve Rsp3_pop1 : stack. 

  Ltac t := 
    match goal with 
        H : Spec.step ?n ?m = Some ?m', 
            Hi : Spec.code_at _ _ = _    
        |- _ =>
        unfold Spec.step in H;
          rewrite Hi in H; 
          unfold Spec.dyncheck in H;
          simpl in H; 
          repeat match type of H with 
                   | context [match ?x with | [] => _ | _::_ => _ end] => 
              destruct (x) eqn:?
                 end;                      
          (repeat match goal with 
                    | H : (check ?x ; _) = _ |- _ => consider x; intros
                  end);
          (try match goal with 
                 | H : Some _ = Some _ |- _ => simpl in H; inject H
                                                       | H : Some _ =  None |- _ => discriminate
                                                       | H : None = Some _ |- _ => discriminate
               end)
    end.

  
  Lemma branch_cond_correct m1 m2 (Hcode : R_code m1 m2) (H : m1 == m2) m1' 
        (Hm1: Spec.step n m1 = Some m1') 
        test
        cond ofs
        (Hi : Spec.code_at (Spec.c m1) (Spec.pc m1) = Some (Spec.Ibranch_cond cond ofs))
        (Hcond : forall x1 y1 x2 y2, 
                   x1 < n -> y1 < n ->
              x1 =%= x2 -> 
              y1 =%= y2 ->
              eval_expr B (test (Evar x2) (Evar y2)) = branch_cond_eval cond x1 y1)
  : 
    match step (Circuit.Ibranch_cond size V test (Evar (mk_val (Spec.pc m1))) (Evar (mk_instr (Spec.Ibranch_cond cond ofs)))) m2 with 
      | None => False
      | Some m2' => m1' == m2'
    end.      
  Proof.
    unfold Spec.step in Hm1; rewrite Hi in Hm1; simpl in Hm1. 
    destruct (Spec.stk m1) as [ | n2 [| n1 s]] eqn: Hs; try discriminate. 
    unfold step. simpl. unfold Sem.Dyn.Bind. unfold Sem.Dyn.OrElse. 
    rewrite (Hcond n1 n2).
    
    destruct cond; simpl in *;
    match goal with 
        |- context [if ?x then _ else _] => consider x; intros
    end;
    unfold Spec.dyncheck in *; simpl in *;
    repeat    match goal with 
        H : context[(check ?x ; _ )] |- _ => consider x; intros
    end;
      try discriminate;
      try match goal with 
          H : Some _ = Some _ |- _ => inject H
      end; simpl; constructor; auto with val; simpl; eauto using Rsp3_pop2; try apply H. 
    
    - apply (Rsp3 _ _ H). rewrite Hs; intuition. 
    - apply (Rsp3 _ _ H). rewrite Hs; intuition. 
    
    - clear Hcond Hm1. 
      destruct H. rewrite (Rstk0 (List.length (Spec.stk m1) - 2)); auto. 
      rewrite Hs. simpl. rewrite List.app_nth1. rewrite List.app_nth2. 
      rewrite List.rev_length. 
      rewrite <- minus_n_O. rewrite minus_diag.  simpl. reflexivity. 
      rewrite List.rev_length. omega.  simpl. 
      auto. 
      auto with val.
    - clear Hcond Hm1. 
      destruct H. rewrite (Rstk0 (List.length (Spec.stk m1) - 1)); auto. 
      rewrite Hs. simpl. rewrite List.app_nth2. 
      rewrite List.app_length.
      rewrite List.rev_length. simpl List.length.  rewrite plus_comm. simpl plus. rewrite minus_diag. simpl. reflexivity. 
      auto with val.
      auto with val. 
  Qed. 

  Lemma Word'eqb_faithful x1 y1:   
    x1 < n -> y1 < n ->
    Word.eqb (mk_val x1) (mk_val y1) = NPeano.Nat.eqb x1 y1.
  Proof. 
    intros. 
    consider (NPeano.Nat.eqb x1 y1); intros. 
    rewrite Word.eqb_correct. 
    unfold mk_val. subst. reflexivity. 
    destruct (Word.eqb (mk_val x1) (mk_val y1)) eqn:H'; intros; trivial.
    exfalso. 
    rewrite Word.eqb_correct in H'. 
    unfold mk_val, Word.repr in H'. injection H'. clear H'. intros H'. 
    rewrite ? Zmod_small in H' by (clear H'; rewrite <- Word.Z'of_nat_power2; zify; omega).
    zify; omega. 
  Qed. 
  
  Lemma Word'leb_faithful x1 y1:   
    x1 < n -> y1 < n ->
    (Word.le (mk_val x1) (mk_val y1))%bool = NPeano.Nat.leb x1 y1.
  Proof. 
    intros. 
    consider (NPeano.Nat.leb x1 y1); intros. 
    rewrite Word.zify_le. simpl. 
    rewrite ? Zmod_small by (rewrite <- Word.Z'of_nat_power2; zify; omega). zify; omega. 
    assert (~ (Word.val (mk_val x1)) <= Word.val (mk_val y1))%Z. simpl. 
    rewrite ? Zmod_small by (rewrite <- Word.Z'of_nat_power2; zify; omega). zify; omega. 
    rewrite <- Word.zify_le in H2.
    destruct (Word.le (mk_val x1) (mk_val y1)); congruence. 
  Qed. 
  
  Lemma Rsp3_push  (y : nat)  s: 
    y < n ->
    (forall x, List.In x s -> x < n) -> 
    (forall x, y = x \/ List.In x s -> x < n). 
  Proof. 
    intros. destruct H; intuition. 
  Qed.

                          (****************)
                          (* MAIN THEOREM *)
                          (****************)
  
  (** * Final theorem: simulation relation for the stack machine *)
  Theorem circuit_correct m1 m2 (Hcode : R_code m1 m2) : 
           m1 == m2 -> 
    forall m1', 
    Spec.step n m1 = Some m1' -> 
    match step (Circuit.Code size V) m2 with 
      | None => False
      | Some m2' => m1' == m2'
    end.
  Proof.     
    intros H m1' Hm1. 
    unfold Next. unfold Circuit.Code, Circuit.code.  
    erewrite step_code_at by eassumption.  Opaque Circuit.case.
    intro_do i Hi.
    rewrite step_case. 

    2: (destruct H as [H1];
        refine (let H := Hcode (Spec.pc m1) _ in _);
        [ eauto |  rewrite Hi in H; tauto]). 
    
    
  
    destruct i; unfold case, type_eq;
    repeat match goal with 
             | |- context [Word.eqb ?x ?y] => replace (Word.eqb x y) with true by reflexivity
             |  |- context [Word.eqb ?x ?y] => replace (Word.eqb x y) with false by reflexivity
           end.    
    - (** Iconst *)
      t.
      Hint Resolve push_correct_stk. 
      constructor; simpl; auto with *; eauto.  
      
      intros. destruct H3. subst.  omega. 
      apply (Rsp3 _ _ H). auto.
      apply H. 
      
    - (** Ivar *)
      t. 
      
      {constructor; simpl; auto with *. 
       + apply push_correct_stk; (try apply H; auto).
       + intros y [H' | H']. apply Rstr2 with (x := x) in H. omega. apply H; auto. 
       + apply H.  
       + apply H.  
      }

    - (** Isetvar *)                        
      t. 
      constructor;simpl; auto with *.
      + apply (pop_correct_stk n s) . rewrite <- Heqs. destruct H.  simpl in *; eauto. 
      + eauto.   
      + eauto with stack. 
      + unfold R_str. simpl.
        intros.
        unfold Spec.update. 
        consider (NPeano.Nat.eqb x i); intros; subst. 
        * rewrite Regfile.gss. 
          eapply stk_1; eauto.  rewrite Word.eqb_correct. reflexivity. 
        * rewrite Regfile.gso. apply H; auto. 
          change (Word.repr size (Z.of_nat x)) with (mk_val x). rewrite (Word'eqb_faithful x i); auto.
          consider (NPeano.Nat.eqb x i); congruence; auto. 
      + unfold R_str. simpl.
        intros i.
        unfold Spec.update. 
        consider (NPeano.Nat.eqb x i); intros; subst. 
        * eapply Rsp3; eauto.  rewrite Heqs. simpl. intuition. 
        * eapply Rstr2; eauto.  

    - t. 
      {
        constructor; simpl; auto with * ; try (solve [apply H]).         
        + intros. 
          eapply push_correct_stk.
          pose ( I := stk_1 m1 m2 n (n0::l) H Heqs). simpl in I. rewrite <- I. clear I. 
          pose ( I := stk_2 m1 m2 n n0 l H Heqs). simpl in I. rewrite <- I. clear I. 
          rewrite plus_comm. apply Rval_add. 

          
          eauto.
 
          replace (List.length l) with (List.length (Spec.stk m1) - 2).
          simpl. rewrite (Rval_sub _ 2). f_equal. destruct H; simpl in *; eauto. rewrite Heqs. simpl. omega. rewrite Heqs. simpl. omega. omega. 
        + eauto. 
        + apply Rsp3_push; auto.   eauto with stack. 
  
      }
    - (** Isub *)
      t. 
      {
        constructor; simpl; auto with *. 
        + intros.  eapply push_correct_stk. 
          pose ( H' := stk_1 m1 m2 n (n0::l) H Heqs). simpl in H'. rewrite <- H'. clear H'. 
          pose ( H' := stk_2 m1 m2 n n0 l H Heqs). simpl in H'. rewrite <- H'. clear H'. 
          apply Rval_sub. 
          auto. 
          eauto. 
          replace (List.length l) with (List.length (Spec.stk m1) - 2). 
          simpl. rewrite (Rval_sub _ 2). f_equal. destruct H. simpl in *. eauto. rewrite Heqs. simpl. omega. rewrite Heqs. simpl. omega.  omega.         
        + eauto. 
        + eapply Rsp3_push; auto. assert (n0 < t.n). intuition. apply Rsp6. rewrite Heqs. simpl; intuition. omega.
          eauto with stack. 
        + apply H. 
        + apply H. 
      }
    -  (** Branch_forward *)
      t. 
        constructor; simpl; auto with *; eauto with *. apply H. 
    -                           (* branch backward *)
      t. constructor; simpl; auto with *; eauto with *. apply H. 
    - destruct c; 
      repeat match goal with 
             | |- context [Word.eqb ?x ?y] => replace (Word.eqb x y) with true by reflexivity
             |  |- context [Word.eqb ?x ?y] => replace (Word.eqb x y) with false by reflexivity
           end;
      apply branch_cond_correct; auto. 
      + intros. simpl. 
        
        rewrite <- H2, <- H3. apply Word'eqb_faithful; auto. 
      + intros; simpl. 
        f_equal. rewrite <- H2, <- H3. apply Word'eqb_faithful; auto. 
      + intros; simpl. 
        rewrite <- H2, <- H3. 
         apply Word'leb_faithful; auto. 
      + intros; simpl. 
        rewrite <- H2, <- H3. 
        replace (Word.lt (mk_val y1) (mk_val x1)) with (negb (Word.le (mk_val x1) (mk_val y1))).
        f_equal. apply Word'leb_faithful; auto. 
        consider (Word.le (mk_val x1) (mk_val y1)); intros;simpl;
        consider (Word.lt (mk_val y1) (mk_val x1)); intros;simpl; try reflexivity. 
        omega. 
        omega. 
        
    - simpl. 
      unfold Spec.step in Hm1; rewrite Hi in Hm1; simpl in Hm1; unfold Spec.dyncheck in Hm1; simpl in Hm1. discriminate. 
  Qed.
  
  (** Sanity check: we verify that the only axiom we depend on is
  functional extensionality (which comes from being used in the
  definition of Word) *)

  Print Assumptions circuit_correct.  
End t. 

Require Compiler.  
Require Import FirstOrder RTL Core.

Definition t := (Compiler.Fesic _ _ (Circuit.Code 8)). 

