module PS = struct
  open Printf
    
  let newpath () = printf "newpath\n"
  let stroke () = printf "stroke\n"
  let moveto (x,y) = printf "%i %i moveto\n" x y 
  let lineto (x,y) = printf "%i %i lineto\n" x y  
  let line a b =
    newpath ();
    moveto a; 
    lineto b;
    stroke ()

  let circle (x,y) r = ()
    (* printf "%i %i %f 0 360 arc closepath\nfill\n" x y r *)

  let header bl ur =
    printf "%%!PS-Adobe-3.0 EPSF-3.0\n";
    printf "%%%%BoundingBox: %i %i %i %i\n" (fst bl) (snd bl) (fst ur) (snd ur);
    printf "newpath\n"
  
  let footer () = 
    printf "stroke\nshowpage\n"
end

module SVG = struct
    
  open Printf
    
  let line (x1,y1) (x2,y2) = 
    printf "<line x1=\"%i\" y1=\"%i\" x2=\"%i\" y2=\"%i\" stroke=\"black\"/>\n"
      x1 y1 x2 y2

  let header bl ur = 
    printf "<svg>\n"

  let footer () = 
    printf "</svg>\n"
end


type 'a tree =
| L of 'a
| N of 'a tree * 'a tree

let rec reverse t =
  match t with 
  | L x -> L x
  | N (l,r) -> N (reverse r, reverse l)

let left t = 
  match t with 
  | N (l,_) -> l
  | _ -> assert false

let right t = 
  match t with 
  | N (l,_) -> l
  | _ -> assert false

module M 
  ( I : sig 
    type t 
    val cmp : t -> t -> t * t 
    val init : int -> t 
  end) = 
struct
  include I
  let rec build n i =
    match n with 
      0 -> L (init i), i+1
    | n -> let (l,i) = build (n - 1) i in 
	   let (r,i) = build (n - 1) i in 
	   N  (l,r), i
  ;;
  let build n = fst (build n 0) ;;


  let rec min_max_swap l r =
    match l,r with 
    | L x, L y -> let (a,b) = cmp x y in L a, L b
    | N (l1,r1), N (l2,r2) -> 
      let (a,b) = min_max_swap l1 l2 in 
      let (c,d) = min_max_swap r1 r2 in 
      (N (a,c), N (b,d))
    | _, _ -> assert false

  let rec merge t = 
    match t with 
    | L x -> t
    | N (l,r) -> let (a,b) = min_max_swap  l r in
		   N (merge a, merge b)

  let rec sort t = 
    match t with 
    | L x -> t
    | N (l,r) -> merge (N (sort l, reverse (sort r)))
end

let comparators = Array.create 32 []

module T = struct
  type t = 
    {
      value : int;
      depth : int
    }
  let f (x,y) = 
    x*10 + 100, y * 10 + 50

  let print a b = 
    let x = max a.depth b.depth in 
    let ya = a.value in 
    let yb = b.value in 
    comparators.(x) <- (ya,yb) :: comparators.(x)
    
  let cmp= 
    (fun x y -> 
      print x y;
      let min x y =
	{value = min x.value y.value; depth = 1 + max x.depth y.depth}
      and max x y = 
	{value = max x.value y.value; depth = 1 + max x.depth y.depth}
      in
      (min x y, max x y))
	
  let init x = {value = x; depth = 0}
end

module Test16 = M (T)

let _ = Test16.(sort (build 4))

(* take a list of segment, and stage them for display *)
let stage l = 
  let intersect (i,j) (x,y) =
    let (i,j) = min i j, max i j in 
    let (x,y) = min x y, max x y in 
    assert (i <= j && x <= y);

    (x <= i && i <= y) || (x <= j && j <= y) 
  in 
  let rec add s = function 
    | [] -> [[s]]
    | l1 :: q -> 
      if List.exists (fun t -> intersect s t) l1
      then l1 :: add s q
      else (s::l1) :: q
  in 
  List.fold_right add l []

let stages = Array.map stage comparators 

(* what is the maximum depth of one stage *)
let m = Array.fold_left (fun acc x -> max acc (List.length x)) 0 stages

(* how many stages do we have *)
let nb_stage = let r = ref 0 in Array.iteri (fun i x -> if x <> [] then r := i;) stages; !r

(* some numerical constants for drawing *)
let dx = m * 2 + 10
let dy = 10

let bl = (0,0) 
let f (x,y) = x + 20, y * dy 
let ur = (40 + nb_stage * dx , 0 + 16 * dy)

(* print the postscript header *)
let _ = SVG.header bl ur


	
(* draw the comparators *)
let _ = 
  for i = 0 to Array.length stages - 1 do
    let rec aux r = function 
      | [] -> ()
      | l :: q -> 	
	List.iter (fun (ya,yb) ->       
	  let x = i * dx + r * 2 in 
	  let a = (x,ya) in 
	  let b = (x,yb) in 
	  SVG.line (f a) (f b);
	) l; 
	aux (r+1) q 
    in 
    aux 0 (    stages.(i) )
  done

(* draw the horizontal lines *)
let _ = 
  for i = 0 to 15 do 
    SVG.line (0, i * dy) (nb_stage * dx + 40,i * dy)
  done

(* ends the drawing *)
let _ = SVG.footer ()

