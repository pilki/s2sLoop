Require List.

Require Polyhedra.
Require OCamlInterface.
(* Standard lib *)
Extract Inductive unit => "unit" [ "()" ].
Extract Inductive bool => "bool" [ "true" "false" ].
Extract Inductive sumbool => "bool" [ "true" "false" ].
Extract Inductive option => "option" [ "Some" "None" ].
Extract Inductive list => "list" [ "[]" "(::)" ].
Extract Inductive prod => "( * )"  [ "(,)" ].

Extract Constant Polyhedra.gen_emptyness_witness =>
  "Empty_wit.gen_emptyness_witness".

Extraction Blacklist List String Int.

Cd "extraction".

Recursive Extraction Library OCamlInterface.
