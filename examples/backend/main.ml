let compile name x = 
  let t = Unix.gettimeofday () in 
  Printf.printf "Compilation of %s\n%!" name;
  match x with 
    Some x ->       
      let b =  (Backend.mk_block name x) in 
      begin 
	Backend.dump b;
	Printf.printf "done (%fs,%i)\n%!" (Unix.gettimeofday () -. t) (List.length b.Backend.bindings)
      end
  | None -> Format.printf "Failed"

(* A low key way to batch compile each one of our examples *)
let _ = compile "Adder" Driver.example1 
let _ = compile "Sorter" Driver.example2
let _ = compile "Stack" Driver.example3
