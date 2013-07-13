open Mlpost
open Point 
open Path 

module PieChart =
struct

  let pi = atan 1. 

  let line a b = pathp ~style:jLine [a;b]
  
  let (--) = line

  let arc ?(r=Num.one) c b e =
    let arc = fullcircle in 
    let b = scale (Num.of_float 2.) (origin -- (dir b)) in 
    let e = scale (Num.of_float 2.) (origin -- (dir e)) in
    shift c (scale (Num.multf 2. r) (cut_before b (cut_after e arc)))


    
  let slice color r b e = 
    let pb = Point.scale r (dir b) in 
    let pe = Point.scale r (dir e) in 
    let path = [origin -- pb; origin -- pe; arc ~r origin b e] in
    let cycle =(build_cycle path) in
    let pen = Pen.scale (Num.bp 0.5) Pen.circle in 
    Command.seq [(* fill ~color cycle; *) draw ~pen cycle]
      
  let piechart r l =
    let rec make acc a = 
      function [] -> acc
      | (n,c,p)::q -> let alpha = p in
		      let acc = Command.append (slice c r a (a +. alpha)) acc in 
		      make acc (a +. alpha) q
    in make Command.nop 0. l
end

let chart = ["", Color.white, 40.;
	     "", Color.white, 50.;
	    ]	

(* let () = Metapost.emit "file_a" ( PieChart.slice Color.red (Num.cm 1.) 0. (40.)) *)
let () = Cairo.emit_png "file_b" ( PieChart.slice Color.red (Num.cm 1.) 40. (50.))
(* let () = Metapost.emit "file_b" (PieChart.piechart (Num.cm 1.) chart) *)
