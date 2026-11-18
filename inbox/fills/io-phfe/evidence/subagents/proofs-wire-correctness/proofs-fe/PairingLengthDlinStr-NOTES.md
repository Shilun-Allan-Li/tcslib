# Pairing.length_dlinStr candidate

Status: independent scratch candidate checked by inspection only; native pending. No Lean,
lake, build, Git, live edit, or extra agent was used. Exact live name is length_dlinStr.
Frozen docstring/header copied byte-for-byte; one tactic block, no holes/sorry, no helper,
no changed serialization or group representation. All lines ≤100 columns.

Read dlinStr_eq, then the six nested lengths with the existing Turing.length_pairEncode
reader `2*|x|+2+|y|`. Each group word has width wG by List.length_ofFn because the field
B.encG is typed G -> Fin wG -> Bool. The five leading group words contribute 10*wG, the
last contributes wG, the description contributes 2*d.length, and six separators contribute
12. omega checks the remaining linear Nat arithmetic.

All simp entries are published equations; no foreign/core/Mathlib definition is explicitly
passed to simp/rw/unfold. No encoding injectivity or group algebra is required.

## Actual searches / exact API references

* Read current live Pairing/Linear.lean:70-103 to preserve dlinStr_eq and the frozen theorem.
* `rg -n '(theorem|lemma) (length_pairEncode|pairEncode_length)|pairEncode_length|length_pairEncode'`
  over TCSlib located the actual published reader TCSlib.Complexity.Turing.length_pairEncode;
  no Candidates-specific replacement was needed.
* Read TCSlib/Complexity/TuringMachine/Encoding.lean:211-226; length_pairEncode is at 220
  and has exact shape `(pairEncode x y).length = 2*x.length+2+y.length`.
* Read Pairing/Group.lean:122-135 for the fixed-width encG field at line 130.
* `rg -n '(theorem|lemma) length_ofFn'` located core List.length_ofFn in
  /Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Init/Data/List/OfFn.lean:40.
  An attempted .lake/packages/lean4/... source path did not exist; the installed toolchain
  path supplied the exact theorem. No conclusion relies on the missing path.
* Read nearby Pairing/Linear.lean:176-190 to verify length_dlinEnc consumes this exact result.
* Searched existing FE/Pairing uses of `length_pairEncode` and `List.length_ofFn` for reuse;
  no additional helper is needed. An initial broad search also named nonexistent
  TCSlib/Computability; corrected to the actual Complexity/TuringMachine/Encoding.lean.

No imports are proposed: the live module already reads dlinStr through Turing.pairEncode,
List.ofFn and the Pairing.Exponents import closure; omega is already available there.
