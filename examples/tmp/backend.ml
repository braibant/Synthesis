

module Src = FirstOrder

type bus_size = int 

let pp_bus_size fmt x = 
  if x = 1 || x = 0  
  then () 
  else  Format.fprintf fmt "[%i:0]" (x - 1)


type nat = int
let rec int_of_nat : int -> int = fun x -> x

let mk_bus_size : int -> bus_size = int_of_nat


type sync =
| Treg of bus_size
| Tregfile of bus_size * int
    
let mk_sync : Src.sync -> sync = function 
  | Src.Treg bus -> Treg (mk_bus_size bus)
  | Src.Tregfile (bus, size) -> Tregfile (mk_bus_size bus, int_of_nat size)

(* using private types to ensure that the traduction is correct *)


module Wire = 
struct 
  type t = string 
  let mk (s: nat) : t = "wire" ^ (string_of_int (int_of_nat s))
end
type wire = Wire.t 

module Memory = 
struct 
  type t = string 
  let mk (s: Src.sync Common.var) : t = 
    let rec aux = function 
      | Common.Coq_var_0 (_,_) -> 0
      | Common.Coq_var_S (_,_,_,q) -> 1 + aux q
    in
    "reg" ^ (string_of_int (aux s))
end
type memory = Memory.t 

type constant = 
  bool * int * string 

type expr =
| E_var   of wire
| E_read  of memory
| E_read_rf of memory * wire
| E_andb  of wire * wire
| E_orb   of wire * wire
| E_xorb  of wire * wire
| E_negb  of wire
| E_eq    of wire * wire
| E_lt    of wire * wire
| E_mux   of wire * wire * wire
| E_plus  of wire * wire
| E_minus of wire * wire
| E_constant of constant  		(* the string is the number in binary form *)
| E_sub of int * int * wire
| E_concat of wire list 
| E_unit 				(* a hack to handle the unit type *)

let mk_constant (n,z) = 
  let rec aux p = 
    match p with 
    | BinNums.Coq_xI p -> (aux p)^"1"
    | BinNums.Coq_xO p -> (aux p)^"0"
    | BinNums.Coq_xH -> "1"
  in 
  let n = int_of_nat n in 
  match z with 
  | BinNums.Z0 -> true, n, "0" 
  | BinNums.Zpos p -> true, n, aux p
  | BinNums.Zneg p -> false, n, aux p
    
let mk_expr (e: Src.expr) : bus_size * expr = 
  let (!) x = int_of_nat x in 
  match e with 
  | Src.E_var (n,w) -> !n,  E_var (Wire.mk w)
  | Src.E_read (n,s) -> !n, E_read (Memory.mk s)
  | Src.E_read_rf (n,_,s,adr) -> !n, E_read_rf (Memory.mk s, Wire.mk adr) (* check *)
  | Src.E_andb (a,b) -> 1, E_andb (Wire.mk a, Wire.mk b)
  | Src.E_orb (a,b) -> 1, E_orb (Wire.mk a, Wire.mk b) 
  | Src.E_xorb (a,b) -> 1, E_xorb (Wire.mk a, Wire.mk b)
  | Src.E_negb (a) -> 1, E_negb (Wire.mk a)
  | Src.E_eq (n,a,b) -> 1, E_eq (Wire.mk a, Wire.mk b)
  | Src.E_lt (n,a,b) -> 1, E_lt (Wire.mk a, Wire.mk b)
  | Src.E_mux (n,c,l,r) -> !n, E_mux (Wire.mk c, Wire.mk l, Wire.mk r)
  | Src.E_plus  (n,a,b) -> !n, E_plus  (Wire.mk a, Wire.mk b)
  | Src.E_minus (n,a,b) -> !n, E_minus (Wire.mk a, Wire.mk b)
  | Src.E_low (i,_,w) -> let i = int_of_nat i in 
			 if i > 0 then 			   
			   i, E_sub (i-1,0, Wire.mk w)
			 else 
			   0, E_unit
  | Src.E_high (n,m,w) -> let n = int_of_nat n in 
			  let m = int_of_nat m in 
			  if m > 0 then 
			    m, E_sub (n+m-1,n, Wire.mk w)
			  else 
			    0, E_unit
  | Src.E_combineLH (n,m,w1,w2)  ->  
    let n = int_of_nat n in 
    let m = int_of_nat m in 
    (n+m), E_concat [Wire.mk w2; Wire.mk w1]
  | Src.E_constant (size,v) -> !size, E_constant (mk_constant (size, v))
  | Src.E_nth (_,_,var,w) -> 
    (* aux returns a pair (i,j) such that i is the index of the
       beginning of the subscript, and i+j-1 is the index of the end of
       the subscript *)
    let rec aux = function 
      | Common.Coq_var_0 (_,n) -> (0,int_of_nat n)
      | Common.Coq_var_S (_,s,_,q) -> let (i,j) = aux q in 
				      (i+ int_of_nat s,j)				 
    in
    let (i,j) = aux var in 
    if j > 0 
    then
      j, E_sub (i+j-1,i,Wire.mk w)
    else
      0, E_unit
  | Src.E_concat (l,dl) -> 
    let rec aux acc = function 
      | DList.DList.Coq_nil -> List.rev acc
      | DList.DList.Coq_cons (_,_,t,q) ->  aux (Wire.mk t :: acc) q 
    in 
    (List.fold_left (fun acc x -> acc + !x) 0 l), E_concat (aux [] dl)

let rec concat sep l = match l with 
  | [] -> ""
  | [t] -> t
  | t :: q -> t ^ sep ^ concat sep q


let pp_expr fmt (e : expr) = 
  match e with 
  | E_var  w -> Format.fprintf fmt "%s" w
  | E_read  m -> Format.fprintf fmt "%s" m
  | E_read_rf  (m,adr) -> Format.fprintf fmt "%s[%s]" m adr
  | E_andb  (a,b) -> Format.fprintf fmt "%s & %s" a b 
  | E_orb   (a,b) -> Format.fprintf fmt "%s | %s" a b 
  | E_xorb   (a,b) -> Format.fprintf fmt "%s ^ %s" a b 
  | E_negb  a ->  Format.fprintf fmt "~ %s" a
  | E_eq    (a,b) -> Format.fprintf fmt "%s == %s" a b 
  | E_lt    (a,b) -> Format.fprintf fmt "%s < %s" a b 
  | E_mux   (c,l,r) -> Format.fprintf fmt "%s ? %s : %s" c l r
  | E_plus  (a,b) -> Format.fprintf fmt "%s + %s" a b 
  | E_minus (a,b) -> Format.fprintf fmt "%s - %s" a b 
  | E_constant (pos,size,value) -> Format.fprintf fmt "%s%i\'b%s" (if pos then "" else "-") size value
  | E_sub (i,j,w) -> 
    assert (i >= j);
    Format.fprintf fmt "%s[%i:%i]" w i j
  | E_concat l -> Format.fprintf fmt "{%s}" (concat ", " l)
  | E_unit -> Format.fprintf fmt "tt"


let pp_bindings fmt (l: (bus_size * expr) list) =
  let i = ref 0 in 
  List.iter 
    (fun (size,expr) -> 
      Format.fprintf fmt "wire %a wire%i = %a;\n"  pp_bus_size size (!i) pp_expr expr;
      incr i
    ) l

type effect = 
| RegisterWrite of (wire * wire) (* (value, guard)  *)
| RegisterFileWrite of (wire * wire * wire ) (* (value,adr,guard) *)

let mk_effect (e : Src.effect option ) : effect option =
  match e with 
  | Some Src.Coq_reg_write (_, value, guard) -> 
    Some (RegisterWrite (Wire.mk value, Wire.mk guard)) 
  | Some Src.Coq_regfile_write (_,_,value, adr, guard) ->
    Some (RegisterFileWrite (Wire.mk value, Wire.mk adr, Wire.mk guard))
  | None -> None


let pp_effect fmt (name, effect)= match effect with 
  | Some (RegisterWrite (value, guard)) ->
    Format.fprintf fmt "if(%s) %s <= %s;\n" guard name value
  | Some (RegisterFileWrite (value, address, guard)) -> 
    Format.fprintf fmt "if(%s) %s[%s] <= %s;\n" guard name address value
  | None -> ()

let pp_init fmt x = ()

let pp_effects fmt initials effects =
  Format.fprintf fmt "always@@(posedge clk)\n";
  Format.fprintf fmt "begin\n";
  begin
    Format.fprintf fmt "\tif(rst_n)\n";
    Format.fprintf fmt "\t\tbegin\n";
    begin 
      Format.fprintf fmt "//INIT \n";
      List.iter (pp_init fmt) initials
    end;
    Format.fprintf fmt "\t\tend\n";
    Format.fprintf fmt "\telse\n";
    Format.fprintf fmt "\t\tbegin\n";
    begin 
      let i = ref 0 in 
      List.iter (fun e -> pp_effect fmt ("reg" ^ string_of_int !i, e); incr i) effects
    end;
    Format.fprintf fmt "\t\tend\n";
  end;
  Format.fprintf fmt "end\n"

let pp_sync fmt (name, ty) = 
  match ty with 
  | Treg bus -> Format.fprintf fmt "input %a reg%i;\n" pp_bus_size bus name
  | Tregfile (bus,length) -> Format.fprintf fmt "input %a reg%i [%i:0];\n" pp_bus_size bus name length

type block =
  {
    name : string;
    output_size : int;
    state : sync list;
    bindings : (bus_size * expr) list;
    effects : (effect option) list;
    initials : unit list;
    value : wire;
    guard : wire;
  }

let mk_block name (b : Src.block) : block =
  let rec convert = function 
    | DList.DList.Coq_nil -> []
    | DList.DList.Coq_cons (t,_,dt,q) -> (t,dt) :: convert q
  in 
  let bindings = 
    List.map 
      (fun (Specif.Coq_existT (_, expr)) ->  mk_expr expr) 
      (b.Src.bindings) in 
  let l = convert b.Src.effects in 
  let (sync, effects) = List.split l in 
  let effects = List.map mk_effect effects in 
  {
    name = name;
    output_size = b.Src.t;
    state = List.map mk_sync sync;
    bindings = bindings;
    effects = effects;
    initials = [];
    value = Wire.mk b.Src.value; 
    guard = Wire.mk b.Src.guard
  }
  
let pp_params fmt l =
  let i = ref 0 in 
  List.iter (fun _ -> Format.fprintf fmt "reg%i," !i; incr i) l

let pp fmt c =
  Format.fprintf fmt "module %s (clk, rst_n, %a guard, value);\n" c.name pp_params c.state;
  Format.fprintf fmt "input clk;\ninput rst_n;\n";
  Format.fprintf fmt "output guard;\noutput [%i:0] value;\n" (c.output_size - 1);
  Format.fprintf fmt "// state declarations\n";
  let i = ref 0 in 
  List.iter (fun s -> pp_sync fmt (!i,s); incr i) c.state;  
  Format.fprintf fmt "// bindings \n";  
  pp_bindings fmt c.bindings;
  Format.fprintf fmt "// effects \n";  
  Format.fprintf fmt "assign guard = %s;\n" c.guard;
  Format.fprintf fmt "assign value = %s;\n" c.value;
  pp_effects fmt c.initials c.effects;
  Format.fprintf fmt "endmodule\n"
    
let dump c = 
  let o = open_out (c.name ^ ".v") in 
  let fmt = Format.formatter_of_out_channel o in 
  let _ = Format.fprintf fmt "%a" pp c in 
  close_out o
  
