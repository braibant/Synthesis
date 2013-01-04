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
    (** Dynamic check that the state we reach is valid  *)
  
    Variable max_pc : nat.
    Definition dyncheck  (s : machine) :=
      if Nat.ltb (pc s) max_pc then 
        Some s
      else None.
    
    Definition step (s : machine) : option machine :=
      do op <- code_at (c s) (pc s);
      match op with 
        | Iconst n => dyncheck (mk (c s) (pc s +1) (n :: stk s) (str s))
        | Ivar x =>   dyncheck (mk (c s) (pc s +1) ((str s) x :: stk s) (str s))
        | Isetvar x => 
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
                           | Cle => NPeano.Nat.leb n1 n2 
                           | Cgt => negb (NPeano.Nat.leb n1 n2)
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
(*             
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
  
  (*
      c   : code;      
      pc : nat;
      stk : stack;
      str : store
   *)
  Definition Phi : state := 
    [
      Tregfile n INSTR;       (* the code *)
      Treg VAL;                  (* the program counter *)
      Tregfile n VAL;         (* the stack *)
      Treg VAL;                 (* the stack pointer *)
      Tregfile n VAL         (* the registers *)     
    ]. 
  
  Ltac set_env := 
    set (CODE  := (var_0) : var Phi (Tregfile n INSTR));
    set (PC    := var_S (var_0) : var Phi (Treg VAL));
    set (STACK := var_S (var_S (var_0)) : var Phi (Tregfile n VAL));
    set (SP    := var_S (var_S (var_S (var_0))) : var Phi (Treg VAL));
    set (REGS  := var_S (var_S (var_S (var_S (var_0)))) : var Phi (Tregfile n INSTR)).
    
  Definition opcode {V} (I : expr V INSTR) : expr V OPCODE. 
    eapply Enth. 2: apply I. apply var_0.  
  Defined. 
  
  Definition val {V} (I : expr V INSTR) : expr V VAL. 
    eapply Enth. 2: apply I. apply var_S. apply var_0. 
  Defined. 
  
  Open Scope action_scope. 
  Notation "x \oplus y" := (OrElse _ _ _ x y) (at level 51, right associativity). 

  Section code. 
    (* We parametrise the following code by the variable parameter of the PHOAS representation.   *)
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
          ((WHEN (cond n1 n2); 
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
        WHEN (opcode i = (#i 11)); 
        ret #b true.
      
      Definition code_at {T} f : action Phi V T:=
        do pc <- ! PC;
        do i  <- read CODE [: pc];
        f pc i.
      
      Fixpoint case {S T} (x : expr V S) (l : list (expr V S * action Phi V T)) default :=
        match l with 
          | nil => default
          | (c,a) :: q => 
            (WHEN (x = c); a) 
              \oplus (WHEN (x <> c); case x q default)
        end. 

      Require Import ZArith. 
      Definition mk_val {n} v : expr V (W n) := (#i (Z.of_nat v)).
                              
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
  Variable n : nat. 

  Notation V := eval_type. 
  
  Definition step  {Phi t} (A : action Phi eval_type t) st : 
    option (eval_state Phi) :=    
    match Sem.eval_action  A st (Diff.init Phi)  with
      | Some p => Some (Diff.apply Phi (snd p) st)
      | None => None
    end. 
  Require Import ZArith DList. 
  Definition mk_val v : eval_type (W n) := Word.repr n (Z.of_nat v).

  Notation "x =%= y" := (mk_val x = y) (at level 80).
  
  Notation c  m2 := (DList.DList.get (Circuit.CODE n) m2).    
  Notation pc m2 := (DList.DList.get (Circuit.PC n) m2).    
  Notation stk m2 := (DList.DList.get (Circuit.STACK n) m2).
  Notation sp m2 := (DList.DList.get (Circuit.SP n) m2).
  (* 
    Definition CODE  := (var_0) : var Phi (Tregfile n INSTR).
    Definition PC    := var_S (var_0) : var Phi (Treg VAL).
    Definition STACK := var_S (var_S (var_0)) : var Phi (Tregfile n VAL).
    Definition SP    := var_S (var_S (var_S (var_0))) : var Phi (Treg VAL).
    Definition REGS  := var_S (var_S (var_S (var_S (var_0)))) : var Phi (Tregfile n VAL).
   *)

  Eval compute in eval_type (Circuit.INSTR 3).
  Require Import ZArith. 

  Definition cast_instr op val : eval_type (Circuit.INSTR n) :=
    (Word.repr _ (Z.of_nat op), (Word.repr _ (Z.of_nat val) , tt)).
  Definition mk_instr (i : Spec.instruction) : eval_type (Circuit.INSTR n) :=
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
  Definition R_code (m1 : Spec.machine) (m2 : eval_state (Circuit.Phi n)) :  Prop :=
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
  
  (** The invariant that relates the execution of the machines  *)
  Record R (m1 : Spec.machine) (m2 : eval_state (Circuit.Phi n)) :  Prop := 
    {
      Rpc1 : Spec.pc m1 =%= pc m2;
      Rpc2 : Spec.pc m1 < n;
      Rstk : R_stk (Spec.stk m1) (stk m2);
      Rsp1 : List.length (Spec.stk m1) =%= sp m2;
      Rsp2 : List.length (Spec.stk m1) < n

    }.

  Hint Resolve Rpc1 Rpc2 Rstk Rsp1 Rsp2. 
  
  Notation "x == y" := (R x y) (at level 80).

  Lemma step_code_at {T} m1 m2 (f : expr V (W n) -> expr V (Circuit.INSTR n) -> 
                                  action (Circuit.Phi n) V T):          
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
  
  Add  Ring wring : (Word.ring n).
    
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
                                      p = mk_val (List.length stk1) ->
                                      List.length stk1 < n -> 
                                      R_stk (x1 :: stk1) (Regfile.set (stk2) p x2).
  Proof. 
    unfold R_stk; simpl. intros Hx H Hp Hstk i i' Hi  Hi' . rewrite <- Hi'. clear Hi'. 
    assert (Hi' : i < List.length stk1 \/ i = (List.length stk1)) by omega; clear Hi.
    destruct Hi' as [Hi | Hi]. 
    * rewrite Regfile.gso. rewrite List.app_nth1 by (rewrite List.rev_length;auto).      
      apply H;auto. 
      simpl in *. 
      clear - Hstk Hi Hp. rewrite Hp. clear Hp. 
      admit.
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
    

          
  Lemma stk_1 m1 m2 a1 a2 s: 
    m1 == m2 -> 
    Spec.stk m1 = a1 :: a2 :: s -> 
    a1 =%= Regfile.get (stk m2) (Word.sub (sp m2) (Cword 1%Z)) . 
  Proof. 
    intros H Heq.
    destruct H as [Hpc1 Hpc2 Hstk Hsp].
    simpl in *. 
    rewrite (Hstk (S(List.length s))); auto. 
    rewrite Heq. simpl. 
    rewrite List.app_nth2. rewrite List.app_length. simpl List.length. rewrite plus_comm. simpl plus. rewrite List.rev_length.  rewrite minus_diag. simpl. reflexivity. 
    auto. 
    rewrite <- Hsp. replace (S (List.length s)) with (List.length (Spec.stk m1) - 1). 
    apply Rval_sub. 
    auto.
    rewrite Heq.  simpl.  reflexivity. 
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
  
  Lemma branch_cond_correct m1 m2 (Hcode : R_code m1 m2) (H : m1 == m2) m1' 
        (Hm1: Spec.step n m1 = Some m1') 
        test
        cond ofs
        (Hi : Spec.code_at (Spec.c m1) (Spec.pc m1) = Some (Spec.Ibranch_cond cond ofs))
        (Hcond : forall x1 y1 x2 y2, 
              x1 =%= x2 -> 
              y1 =%= y2 ->
              eval_expr B (test (Evar x2) (Evar y2)) = branch_cond_eval cond x1 y1)
  : 
    match step (Circuit.Ibranch_cond n V test (Evar (mk_val (Spec.pc m1))) (Evar (mk_instr (Spec.Ibranch_cond cond ofs)))) m2 with 
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
    match goal with 
        H : context[(check ?x ; _ )] |- _ => consider x; intros
    end;
      try discriminate;
    match goal with 
        H : Some _ = Some _ |- _ => inject H
    end; simpl; 
    constructor; simpl; eauto with *. 
    
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

                          (****************)
                          (* MAIN THEOREM *)
                          (****************)
  
  Theorem circuit_correct m1 m2 (Hcode : R_code m1 m2) : 
           m1 == m2 -> 
    forall m1', 
    Spec.step n m1 = Some m1' -> 
    match step (Circuit.Code n V) m2 with 
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
        [admit |  rewrite Hi in H; tauto]). 
    
    
  
    destruct i; unfold case, type_eq;
    repeat match goal with 
             | |- context [Word.eqb ?x ?y] => replace (Word.eqb x y) with true by reflexivity
             |  |- context [Word.eqb ?x ?y] => replace (Word.eqb x y) with false by reflexivity
           end.
    - (** Iconst *)
      unfold Spec.step in Hm1; rewrite Hi in Hm1;simpl in Hm1; unfold Spec.dyncheck in Hm1; simpl in Hm1; match goal with | H : context [NPeano.Nat.ltb ?x ?y] |- _ => destruct (NPeano.Nat.ltb x y) eqn:? end; simpl in Hm1.  inject Hm1. 
      simpl. Transparent DList.get. Transparent Diff.apply.       simpl. 
      Hint Resolve push_correct_stk. 
      constructor; simpl; auto with *; eauto with *.
       discriminate. 
    - (** Ivar *)
      unfold Spec.step in Hm1; rewrite Hi in Hm1;simpl in Hm1; unfold Spec.dyncheck in Hm1; simpl in Hm1; match goal with | H : context [NPeano.Nat.ltb ?x ?y] |- _ => destruct (NPeano.Nat.ltb x y) eqn:? end; simpl in Hm1.  inject Hm1.
      
      {constructor; simpl; auto with *; eauto with *.
       + apply push_correct_stk. admit. auto. destruct H; simpl in *; auto. 
      }
      discriminate. 

    - (** Isetvar *)                        
      unfold Spec.step in Hm1; rewrite Hi in Hm1;simpl in Hm1; unfold Spec.dyncheck in Hm1; simpl in Hm1; match goal with | H : context [NPeano.Nat.ltb ?x ?y] |- _ => destruct (NPeano.Nat.ltb x y) eqn:? end; simpl in Hm1; destruct (Spec.stk m1) eqn:?; try discriminate. inject Hm1.  
      simpl.  
      constructor;simpl; auto with *; eauto with *. 
      + apply (pop_correct_stk n0 s) . rewrite <- Heqs. destruct H.  simpl in *; eauto. 
    - unfold Spec.step in Hm1; rewrite Hi in Hm1;simpl in Hm1; unfold Spec.dyncheck in Hm1; simpl in Hm1; match goal with | H : context [NPeano.Nat.ltb ?x ?y] |- _ => destruct (NPeano.Nat.ltb x y) eqn:? end; simpl in Hm1;  destruct (Spec.stk m1) as [ | a1 [ |a2 s]] eqn:?; try discriminate. inject Hm1.  
      {
        constructor; simpl; auto with *; eauto with *. 
        + intros. 
          eapply push_correct_stk.
          pose ( H1 := stk_1 m1 m2 a1 a2 s H Heqs). simpl in H1. rewrite <- H1. clear H1. 
          pose ( H2 := stk_2 m1 m2 a1 a2 s H Heqs). simpl in H2. rewrite <- H2. clear H2. 
          rewrite plus_comm. apply Rval_add. 

          
          eauto.
 
          replace (List.length s) with (List.length (Spec.stk m1) - 2).
          simpl. rewrite (Rval_sub _ 2). f_equal. destruct H; simpl in *; eauto. rewrite Heqs. simpl. omega. rewrite Heqs. simpl. omega. 
      }
    - (** Isub *)
      unfold Spec.step in Hm1; rewrite Hi in Hm1;simpl in Hm1; unfold Spec.dyncheck in Hm1; 
      simpl in Hm1; destruct (Spec.stk m1) as [ | a1 [ |a2 s]] eqn:?; try discriminate;
      repeat (match goal with 
                | H : context [ check ?x; _ ] |- _ => consider x; intros
              end); try discriminate.       
      inject H2.
      {
        constructor; simpl. 
        + auto with val. 
        + auto. 
        + intros.  eapply push_correct_stk. 
          pose ( H' := stk_1 m1 m2 a1 a2 s H Heqs). simpl in H'. rewrite <- H'. clear H'. 
          pose ( H' := stk_2 m1 m2 a1 a2 s H Heqs). simpl in H'. rewrite <- H'. clear H'. 
          apply Rval_sub. 
          auto. 
          eauto. 
          replace (List.length s) with (List.length (Spec.stk m1) - 2). 
          simpl. rewrite (Rval_sub _ 2). f_equal. destruct H. simpl in *. eauto. rewrite Heqs. simpl. omega. rewrite Heqs. simpl. omega. 
        + eauto using pop_correct_sp. 
      }
    -  (** Branch_forward *)
      unfold Spec.step in Hm1; rewrite Hi in Hm1;simpl in Hm1; unfold Spec.dyncheck in Hm1; simpl in Hm1; match goal with | H : context [NPeano.Nat.ltb ?x ?y] |- _ => destruct (NPeano.Nat.ltb x y) eqn:? end; simpl in Hm1; try discriminate. inject Hm1.
      {
        constructor; simpl; auto with *; eauto with *. 
      }      
    - 
      unfold Spec.step in Hm1; rewrite Hi in Hm1;simpl in Hm1; unfold Spec.dyncheck in Hm1; simpl in Hm1.  
      consider (NPeano.leb ofs (Spec.pc m1 + 1)); intros Hofs; try discriminate. 
      consider (NPeano.Nat.ltb (Spec.pc m1 + 1 - ofs) n); intros Hofs'; try discriminate. 
      intros Hm. inject Hm. 
      simpl. 
      {
        constructor; simpl; auto with *; eauto with *.  
      } 
    - destruct c; 
      repeat match goal with 
             | |- context [Word.eqb ?x ?y] => replace (Word.eqb x y) with true by reflexivity
             |  |- context [Word.eqb ?x ?y] => replace (Word.eqb x y) with false by reflexivity
           end;
      apply branch_cond_correct; auto. 
      + clear. intros. simpl. rewrite <- H, <- H0.
        admit. 
      + clear. intros. simpl. rewrite <- H, <- H0.
        admit. 
      + clear. intros. simpl. rewrite <- H, <- H0.
        admit. 
      + clear. intros. simpl. rewrite <- H, <- H0.
        admit. 
    - simpl. 
      unfold Spec.step in Hm1; rewrite Hi in Hm1; simpl in Hm1; unfold Spec.dyncheck in Hm1; simpl in Hm1. discriminate. 
  Qed.

  Print Assumptions circuit_correct. 
Require Compiler. 
Require Import FirstOrder RTL Core. 

Definition t := (Compiler.fesiopt _ _ (Code 8)). 


(* Definition finish {Phi t} x := List.length (FirstOrder.bindings Phi t(FirstOrder.compile _ _ x)).  *)
(* Eval vm_compute in finish (Compiler.Compile _ _ (Ex2.Code 4) _).  *)
(* Definition step {Phi t} x :=  (CSE.Compile Phi t  (CP.Compile _ _ x)).  *)
(* Eval vm_compute in finish (step (Compiler.Compile _ _ (Ex2.Code 4) ) _).  *)
(* Eval vm_compute in finish (step (step (Compiler.Compile _ _ (Ex2.Code 4) )) _).  *)
(* Eval vm_compute in finish (step (step (step (Compiler.Compile _ _ (Ex2.Code 4) ))) _).  *)



