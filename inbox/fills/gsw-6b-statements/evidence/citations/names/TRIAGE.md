# Sketch-name check (lead), against the final declarations

`NameCheck.lean` runs `#check @X` on every backticked identifier-like token (containing `_` or `.`)
in the docstrings of the 12 new and changed files (216 tokens), inside the GSW namespace with
`BoolCircuit`, `BranchingProgram`, `Complexity`, `Encryption.PublicKey`, `FormulaArith` and the
LWE namespaces open. 43 tokens fail; `NameCheck2.lean` re-checks the plausible lemma names with their
full namespaces (20/20 resolve). Triage of the 43:
- dot-notation names written relative to `DAGCircuit` (`depthAt_gate`, `depthAt_input`, `depth_eq`,
  `values_eq`, `isLayered_iff`, `isNANDForm_iff`, `layerNAND_*`, `toNANDForm_*`, `Cc.args_lt`,
  `Cc.output_lt`, `Cc.depth`, `Cc.eval`): resolve as `BoolCircuit.DAGCircuit.*` (NameCheck2);
- `LWE.Family` fields `dimension_le`, `samples_le`, `modulus_le_pow`, and `ratioBounded_iff`
  (`LWE.Family.ratioBounded_iff`), `P.modulus_le` (field `Parameters.modulus_le`): resolve (NameCheck2);
- `negligible_polyExpr_mul`: `TCSlib.Cryptography.EnsembleLemmas.negligible_polyExpr_mul`
  (`Asymptotic/EnsemblesLemmas.lean:377`), cited with that file;
- `decrypt_eq_decode_errorSum`: the private lemma of `GSW/Scheme.lean:213`, named as such;
- `ring_nf`: a tactic; `EnsembleSecurity.lean`: a file name; `_singleton`, `_cons_cons`: suffixes
  of `bootGate_of_args_eq_*` written in short form;
- mathematical variables in code font: `G_0`, `G_N`, `G_i`, `H_0`, `H_L`, `H_e`, `H_h`, `pk_0`,
  `s_0`, `s_d`, `s_e`, `c`, `c_dec`, `v`.
One real error was found before this check by the probe sub-agent and fixed: G16's sketch named
`Nat.clog_le_self`, which does not exist in the pinned Mathlib; it now names
`Nat.clog_le_iff_le_pow` and `Nat.lt_two_pow_self` (both resolve).
