These files contain the compiler part of the development associated
with the paper "Formal verification of Hardware Synthesis". 

Running make in this directory will compile this development. However,
in order to visit these files, one must either
- run coqtop, and execute the command 
  Add Rec LoadPath "./" as Synthesis.
- run coqtop with the option 
  -R "path_to_the_src_folder" "Synthesis"


