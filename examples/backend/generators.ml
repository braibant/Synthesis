let version = "0.1"

let compile tag name x = 
  let t = Unix.gettimeofday () in 
  Printf.printf "Compilation of %s\n%!" name;
  match x with 
    Some x ->       
      let b =  (Backend.mk_block tag name x) in 
      begin 
	Backend.dump b;
	Printf.printf "done (%fs,%i)\n%!" (Unix.gettimeofday () -. t) (List.length b.Backend.bindings)
      end
  | None -> Format.printf "Failed"



let args = ["-adder", 
	    Arg.Int (fun n -> 
	      let tag = Printf.sprintf "adder%i_%s" n version in
	      compile tag "Adder" (Driver.adder n)), 
	    "compile the adder core for numbers of size [2^n]"; 
	    
	    "-sorter", 
	    Arg.Int (fun n ->
	      let tag = Printf.sprintf "sorter%i_%s" n version in
	      compile tag "Sorter" (Driver.sorter n)), 
	    "compile a sorter core for [2^n] arguments of bitwidth 4 (hard-coded)"; 
	    
	    "-stack", 
	    Arg.Unit (fun _ -> 
	      let tag = Printf.sprintf "stack_%s" version in
	      compile tag "Stack" Driver.stack), 
	    "compiler the stack core"; 	    
	   ]

let usage = Printf.sprintf "run %s with the right option to produce the corresponding core" Sys.argv.(0)

let _ = if Array.length Sys.argv = 1 then Arg.usage args usage
let _ = Arg.parse args (fun _ -> ()) usage
