# Wire groupVector_length: one-row adapter

Exact searched header/opening prose preserved. One tactic block; no new helper, import,
definition, admission, flatten length/count argument, or native execution. No Lean/lake/
Git command or live edit was run. Root native validation remains pending.

The whole mathematical fact is the EXISTING pp.group.length_groupMatrixEnc applied to
the one-row matrix fun (_ : Fin 1) (j : Fin n) => v j. Equation readers groupVector_eq
and BilinearGroup.groupMatrixEnc_eq identify the inner vector word. List.ofFn_const,
List.replicate_one and List.flatten_singleton remove only the singleton OUTER row list.
Nat.one_mul simplifies its row count. There is no List.length_flatten/List.length_ofFn
calculation or independent point-block counting proof.

Rule 10: every supplied simp entry is a published reader/theorem; no public definition
body is supplied. The matrix lambda is merely a typed view of the existing vector,
not an additional runtime representation. Empty vector dimensions remain included.
The proof depends on the published base matrix API, not the pending Wire matrix wrapper.

Static exact APIs read:
- Pairing/MatrixDH/Defs.lean:60 groupMatrixEnc_eq; :68 length_groupMatrixEnc.
- Wee20/Wire.lean groupVector_eq.
- Mathlib/Data/List/OfFn.lean:117 ofFn_const.
- Core Init/Data/List/Lemmas.lean:2120 replicate_one; :1875 flatten_singleton.
- Existing Nat.one_mul.
Root's evidence/search/wire-words/run supplied the prior clean typing/exact/apply gate.
No mathematical obstruction found. Other helper bodies were not changed.
