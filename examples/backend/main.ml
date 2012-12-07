let compile name x = 
  let t = Unix.gettimeofday () in 
  Printf.printf "Compilation of %s\n%!";
  match x with 
    Some x ->       
      Backend.dump (Backend.mk_block name x);
      Printf.printf "done (%fs)\n%!" (Unix.gettimeofday () -. t)
  | None -> Format.printf "Failed"

let _ = compile "Cpu" Driver.example1
let _ = compile "Adder" Driver.example2 
let _ = compile "Stack" Driver.example3
let _ = compile "Sorter" Driver.example4
