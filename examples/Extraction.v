Require Driver. 

Set Extraction AccessOpaque.

Cd "tmp".

Extraction Blacklist String List.

Extract Inductive bool => bool [ true false ].
Extract Inductive option => option [ Some None ].
Extract Inductive unit => unit [ "()" ].
Extract Inductive list => list [ "[]" "( :: )" ].
Extract Inductive prod => "( * )" [ "" ].

(** NB: The "" above is a hack, but produce nicer code than "(,)" *)

(** Mapping sumbool to bool and sumor to option is not always nicer,
    but it helps when realizing stuff like [lt_eq_lt_dec] *)

Extract Inductive sumbool => bool [ true false ].
Extract Inductive sumor => option [ Some None ].

(** Restore lazyness of andb, orb.
    NB: without these Extract Constant, andb/orb would be inlined
    by extraction in order to have lazyness, producing inelegant
    (if ... then ... else false) and (if ... then true else ...).
*)

Extract Inlined Constant andb => "(&&)".
Extract Inlined Constant orb => "(||)".

Extract Constant Common.admit => "Obj.magic ()".

Extract Inductive nat => int [ "0" "Pervasives.succ" ]
 "(fun fO fS n -> if n=0 then fO () else fS (n-1))".

(** Efficient (but uncertified) versions for usual [nat] functions *)

Extract Constant plus => "(+)".
Extract Constant pred => "fun n -> max 0 (n-1)".
Extract Constant minus => "fun n m -> max 0 (n-m)".
Extract Constant mult => "( * )".
Extract Inlined Constant max => max.
Extract Inlined Constant min => min.
(*Extract Inlined Constant nat_beq => "(=)".*)
Extract Inlined Constant EqNat.beq_nat => "(=)".
Extract Inlined Constant EqNat.eq_nat_decide => "(=)".

Extract Inlined Constant Peano_dec.eq_nat_dec => "(=)".

Extract Constant Compare_dec.nat_compare =>
 "fun n m -> if n=m then Eq else if n<m then Lt else Gt".
Extract Inlined Constant Compare_dec.leb => "(<=)".
Extract Inlined Constant Compare_dec.le_lt_dec => "(<=)".
Extract Constant Compare_dec.lt_eq_lt_dec =>
 "fun n m -> if n>m then None else Some (n<m)".

Extract Constant Even.even_odd_dec => "fun n -> n mod 2 = 0".
Extract Constant Div2.div2 => "fun n -> n/2".

Recursive Extraction Library Driver. 

