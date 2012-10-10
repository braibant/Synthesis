let compile name x = 
  match x with 
    Some x ->  Backend.dump (Backend.mk_block name x)
  | None -> Format.printf "Failed"

let _ = compile "Cpu" Driver.example1
let _ = compile "Adder" Driver.example2 
