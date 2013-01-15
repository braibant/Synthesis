This directory contains our various examples, as well as our prototype
OCaml back-end. 

- Add.v contains the definition of a parametric divide and conquer
  adder (no proof).
- Sorter.v contains the definition and the proof of correction of the
  sorter core.
- Stack.v contains the definition and the proof of correction of the
  stack machine. (fibonacci.ml contains a toy compiler from IMP to the
  byte-code that is understood by the stack machine.)
- test_* contains examples of the outputs of the compiler on the
  aforementionned examples, along with test drivers that makes it
  possible to execute them with iVerilog. 
- backend/ contains the code that implements the OCaml backend, as
  well as the OCaml driver. 


Running [make] in this directory build the OCaml back-end.  This
produces an executable [generators.native] that generates cores
corresponding to the aforementionned examples. We refer the author to
the examples we put in the test_/* directory for guidance about how to
use these cores. [make demo] rebuilds these tests in the [verilog/]
directory.

