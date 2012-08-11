type var = string;;

type ('a,'b) map = ('a * 'b) list

type expr = | False | True | N of int

let pp fmt x = match x with 
  | True -> Format.fprintf fmt "T"
  | False -> Format.fprintf fmt "F"
  | N x -> Format.fprintf fmt "%i" x


type node = (expr * var * expr)

type bdd =
    {
      t : (int , node) map;
      h : (node, int) map ;
      next : int
    }
  	
let empty = {t = []; h = []; next = 0}

let node bdd (l : expr) v (h : expr) = 
  if l = h then l,bdd
  else 
    try 
      N (List.assoc (l,v,h) bdd.h), bdd 
    with 
	Not_found -> 	 
	  let n = (l,v,h) in 
	  let u = bdd.next in 
	  let bdd = {t = (u,n) :: bdd.t; 
		     h = (n,u) :: bdd.h;
		     next = u + 1} in 
	  (N u,bdd)
;;
      
module Op = struct
    
  let rec andb bdd (a : expr) (b : expr) : expr * bdd =
    match a,b with 
      | False, _ | _, False -> False, bdd
      | True, f | f, True -> f, bdd
      | N a, N b -> 
	let (l1,v1,h1) = List.assoc a bdd.t  in 
	let (l2,v2,h2) = List.assoc b bdd.t  in 
	if v1 = v2
	then 
	  let (x,bdd) = andb bdd l1 l2 in 
	  let (y,bdd) = andb bdd h1 h2 in 
	  node bdd x v1 y
	else if v1 < v2 then 
	  let x,bdd = andb bdd l1 (N b) in 
	  let y,bdd = andb bdd h1 (N b) in 
	  node bdd x v1 y
	else 	
	  let x,bdd = andb bdd (N a) l2 in 
	  let y,bdd = andb bdd (N a) h2 in 
	  node bdd x v2 y

  let rec orb bdd (a : expr) (b : expr) : expr * bdd =
    match a,b with 
      | False, f | f, False -> f, bdd
      | True, _ | _, True -> True, bdd
      | N a, N b -> 
	let (l1,v1,h1) = List.assoc a bdd.t  in 
	let (l2,v2,h2) = List.assoc b bdd.t  in 
	if v1 = v2
	then 
	  let (x,bdd) = orb bdd l1 l2 in 
	  let (y,bdd) = orb bdd h1 h2 in 
	  node bdd x v1 y
	else if v1 < v2 then 
	  let x,bdd = orb bdd l1 (N b) in 
	  let y,bdd = orb bdd h1 (N b) in 
	  node bdd x v1 y
	else 	
	  let x,bdd = orb bdd (N a) l2 in 
	  let y,bdd = orb bdd (N a) h2 in 
	  node bdd x v2 y


  let rec negb bdd a  =
    match a with 
      | True -> False,bdd
      | False -> True,bdd
      | N a -> 	
	let (l,v,h) = List.assoc a bdd.t  in 
	let x, bdd = negb bdd l in 
	let y, bdd = negb bdd h in 
	node bdd x v y

  let var bdd a =
    node bdd False a True

  type t = bdd -> expr * bdd

  let (&&) (a : t) (b : t) : t = fun bdd -> 
    let (a, bdd) = a bdd in 
    let (b, bdd) = b bdd in 
    andb bdd a b

  let (||) (a : t) (b : t) : t = fun bdd -> 
    let (a, bdd) = a bdd in 
    let (b, bdd) = b bdd in 
    orb bdd a b
    
  let not (a : t) : t = fun bdd -> 
    let (a,bdd) = a bdd in negb bdd a
			
  let run (a : t) x : expr * bdd = a x 

  let var x : t = fun bdd -> var bdd x
    
  let (=>) a b = not a || b
    
end      
 


let middle x = Op.(x || not x) 
let contradiction x = Op.(not (x && not x))
let chain x y = Op.(x || not y)

  
  
let _ = 
  let test x = Op.(x || (not x )) in 
  Op.(run (test (var "x" && var "y" || var "x")) empty)

let _ =
  Op.(run (chain (var "x") (chain (var "y") (chain (var "z") (var "x"))) || not (var "x")) empty)

let _ = Op.(run (var "x" || not (not (var "x"))) empty )

let _ = Op.(run ((var "a" && var "b" && var "c") => var "a") empty);;
  
