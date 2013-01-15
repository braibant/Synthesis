type reg = int

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

type env =
  {
    reg : int array; 
    stack   : int array; 
    mutable sp : int;
    code: instr array;
    mutable pc  : int;     
  }

exception Halt

let eval env = 
  (* Printf.printf "pc:\t%i; sp:\t%i\n" env.pc env.sp; *)
  let push i = 
    env.stack.(env.sp) <- i; 
    env.sp <- env.sp + 1
  in 
  let pop () = 
    env.sp <- env.sp - 1;
    env.stack.(env.sp)
  in 
  match env.code.(env.pc) with 
  | Iconst i -> 
    push i;
    env.pc <- env.pc + 1
  | Ivar r -> 
    push (env.reg.(r));
    env.pc <- env.pc + 1
  | Isetvar r -> 
    let v = pop () in 
    env.reg.(r) <- v;
    env.pc <- env.pc + 1       
  | Iadd -> 
    let n2 = pop () in 
    let n1 = pop () in 
    push (n1 + n2);
    env.pc <- env.pc + 1
  | Isub -> 
    let n2 = pop () in 
    let n1 = pop () in 
    push (n1 - n2);
    env.pc <- env.pc + 1
  | Ibranch_forward ofs -> 
    env.pc <- env.pc + 1 + ofs
  | Ibranch_backward ofs -> 
    env.pc <- env.pc + 1 - ofs
  | Ibeq ofs -> 
    let n2 = pop () in 
    let n1 = pop () in 
    if n1 = n2 then 
      env.pc <- env.pc + 1 + ofs
    else 
      env.pc <- env.pc + 1 
  | Ibne ofs -> 
    let n2 = pop () in 
    let n1 = pop () in 
    if n1 <> n2 then 
      env.pc <- env.pc + 1 + ofs
    else 
      env.pc <- env.pc + 1 
 | Ible ofs -> 
    let n2 = pop () in 
    let n1 = pop () in 
    if n1 <= n2 then 
      env.pc <- env.pc + 1 + ofs
    else 
      env.pc <- env.pc + 1 
 | Ibgt ofs -> 
   let n2 = pop () in 
   let n1 = pop () in 
    if n1 > n2 then 
      env.pc <- env.pc + 1 + ofs
    else 
      env.pc <- env.pc + 1 
  | Ihalt -> raise Halt

 
type aexp =
  ANum of int 
| AId of reg
| APlus of aexp * aexp
| AMinus of aexp * aexp 

let rec compile_aexp = function 
  | ANum i -> [Iconst i]
  | AId v -> [Ivar v]
  | APlus (a1, a2) -> (compile_aexp a1) @ (compile_aexp a2) @ [Iadd]
  | AMinus (a1, a2) -> (compile_aexp a1) @ (compile_aexp a2) @ [Isub]

type bexp =
| BTrue
| BFalse
| BEq of aexp * aexp
| BLe of aexp * aexp
| BNot of bexp
| BAnd of bexp * bexp

let rec compile_bexp cond ofs =  function 
  | BTrue -> if cond then [Ibranch_forward ofs] else []
  | BFalse -> if cond then [] else  [Ibranch_forward ofs] 
  | BEq (a1,a2) -> (compile_aexp a1) @ (compile_aexp a2) @
    if cond then [Ibeq ofs] else [Ibne ofs]
  | BLe (a1,a2) -> (compile_aexp a1) @ (compile_aexp a2) @
    if cond then [Ible ofs] else [Ibgt ofs]
  | BNot b1 -> 
    compile_bexp (not cond) ofs b1
  | BAnd (b1,b2) -> 
    let c2 = compile_bexp cond ofs b2 in 
    let c1 = compile_bexp false (if cond then List.length c2 else ofs + List.length c2) b1 in 
    c1 @ c2
;;
    

type com =
| CSkip 
| CAss of reg * aexp
| CSeq of com * com 
| CIf of bexp * com * com    
| CWhile of bexp * com 

let rec compile_com = function 
  | CSkip -> []
  | CAss (id,a) -> compile_aexp a @ [Isetvar id]
  | CSeq (c1, c2) -> compile_com c1 @ compile_com c2
  | CIf (b,ifso,ifnot) -> 
    let code_ifso = compile_com ifso in 
    let code_ifnot = compile_com ifnot in 
    (compile_bexp false (List.length code_ifso + 1) b) 
    @ code_ifso 
    @ [Ibranch_forward (List.length code_ifnot)] 
    @ code_ifnot
  | CWhile (b,body) -> 
    let code_body = compile_com body in 
    let code_test = compile_bexp false (List.length code_body + 1) b in 
    code_test 
    @ code_body
    @ [Ibranch_backward ((List.length code_test) + (List.length code_body) + 1)]
;;

module Imp = struct
  let (!) x = AId x
  let (:=) x y = CAss (x,y) 
  let (&) x y  = CSeq (x,y)    
  let const x = ANum x
  let (&&) x y = BAnd (x,y)
  let not x = BNot x
  let (||) x y = not (not x && not y)
  let (<=) x y =  BLe (x,y)
  let (==) x y  =  BEq (x,y)
  let (<) x y =  x <= y && not (x == y) 
  let (+) x y = APlus (x,y)
end
  
let fib n =  
  let mk_var = let r = ref 0 in 
	       fun () -> let v = !r in incr r; v
  in
  Imp.(
    let return = mk_var () in 
    let fib = mk_var () in 
    let prev = mk_var () in 
    let temp = mk_var () in 
    let i = mk_var () in 
    CIf ((n < const 2), (return:= n), CSkip) 
    & (prev := const 0)
    & (fib := const 1)
    & (i := const 1)
    & (CWhile ((!i < n), 
	       (temp := !fib + !prev)
	       & (prev := !fib)
	       & (fib := !temp)
	       & (i := !i + const 1))
    )
    & (return := !fib)
  )
;;

let mk_env nb_reg nb_stack code =  
  {
    reg = Array.create nb_reg 0;
    stack = Array.create nb_stack 0; 
    sp = 0;
    code = Array.of_list code; 
    pc = 0      
  }
;;


let fib_env = 
  let code = compile_com (fib (Imp.const 15)) in 
  let env = mk_env 16 64 (code @ [Ihalt]) in 
  env

let _ = fib_env.code.(23);;

let pp_opcode i arg = 
  let to_string size n = 
    let s = String.create size in 
    let k = ref n in 
    for i = size - 1 downto 0 do
      if ! k mod 2 = 0 then 
	s.[i] <- '0'
      else 
	s.[i] <- '1';
      k := !k / 2
    done;
    s
  in 	        
  Printf.sprintf  "%i\'b%s%s" (8 + 4) (to_string 8 arg) (to_string 4 i)
;;

pp_opcode 0 15;;
pp_opcode 0 2;;

let pp_instr = function 
  | Iconst i ->       
    pp_opcode 0 i 
  | Ivar r -> 
    pp_opcode 1 r
  | Isetvar r -> 
    pp_opcode 2 r
  | Iadd -> 
    pp_opcode 3 0
  | Isub -> 
      pp_opcode 4 0
  | Ibranch_forward ofs -> 
    pp_opcode 5 ofs 
  | Ibranch_backward ofs -> 
    pp_opcode 6 ofs
  | Ibeq ofs -> 
    pp_opcode 7 ofs
  | Ibne ofs -> 
    pp_opcode 8 ofs
  | Ible ofs -> 
    pp_opcode 9 ofs
  | Ibgt ofs -> 
    pp_opcode 10 ofs
  | Ihalt  -> 
    pp_opcode 11 0

let init name env = 
  (* assume size is 8 *)  
  for i = 0 to Array.length env.code -1 do
    Printf.printf "%s[%i] = %s;\n" name i (pp_instr env.code.(i))
  done

(** use the following code to generate a bitmap for the stack machine  *)
let _ = 
  let env = 
    let code = compile_com (fib (Imp.const 10)) in 
    let env = mk_env 16 64 (code @ [Ihalt]) in 
    env
  in 
  init "reg_0" env


let pp_env env = 
  Printf.printf "pc:%i\t sp:%i\n" env.pc env.sp;
  Printf.printf "code at pc: %s\n%!" (pp_instr env.code.(env.pc)); 
  for i = 0 to 7 do 
    Printf.printf "stack[%i]: %8i\n%!" i env.stack.(i);
  done;
  for i = 0 to 7 do 
    Printf.printf "store [%i]: %8i\n%!" i env.reg.(i);
  done;
;;

(* use this piece of code to execute the ocaml version of the stack
   machine till it reaches the end *)

let test interactive = 
  let code = compile_com (fib (Imp.const 10)) in 
  let env = mk_env 16 64 (code @ [Ihalt]) in 
  try 
    while true do
      if interactive then 
	begin
	  ignore(read_line ());
	  pp_env env;
	  eval env	
	end
      else
	begin
	  pp_env env;
	  eval env	
	end
	  
    done;
    env
  with Halt -> env
    
let _ = test false;;


