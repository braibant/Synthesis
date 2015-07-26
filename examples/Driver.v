Require SynthExamples.Add SynthExamples.Stack SynthExamples.Sorter.

(** Produces an adder for numbers of size [2^n]  *)
Definition adder n := (Compiler.Fesic _ _  (Add.generator n)).

(** Produces a sorter core for [2^n] numbers. *)
Definition sorter n := (Compiler.Fesic _ _  (Sorter.generator 4 n)).

(** Produces the stack machine core. Parameters must be set in the corresponding Coq file. *)
Definition stack := Stack.t.
