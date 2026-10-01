/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang, Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.CircuitComplexity.Formulas
import TCSlib.Complexity.CircuitComplexity.DecisionTree
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.CircuitComplexity.CircuitSat
import TCSlib.Complexity.CircuitComplexity.Encoding
import TCSlib.Complexity.CircuitComplexity.Universal
import TCSlib.Complexity.CircuitComplexity.HardFunctions
import TCSlib.Complexity.CircuitComplexity.NCAC
import TCSlib.Complexity.CircuitComplexity.Parity
import TCSlib.Complexity.CircuitComplexity.Hierarchy
import TCSlib.Complexity.CircuitComplexity.UnaryLanguages
import TCSlib.Complexity.CircuitComplexity.UHalt
import TCSlib.Complexity.CircuitComplexity.SizeClasses

/-!
# Circuit Complexity

Boolean circuits and formulas, the class `P/poly`, and Arora–Barak §6.1.

## Contents

- `CircuitComplexity.Basic`: `BoolCircuit.Lit`, the general circuit tree
  `BoolCircuit.Circuit` (unbounded fan-in) with `eval` / `litCount` / `depth` /
  `size` / `maxFanin`, and the alternating normal forms
  `NAndCircuit` / `NOrCircuit` with `toNAnd` / `toNOr` and the forgetful map
  `toCircuit`.
- `CircuitComplexity.Formulas`: `Literal`, `Term`, `DNF`, `CNF` with `eval`
  and `width`.
- `CircuitComplexity.DecisionTree`: `DecisionTree` with `eval`, `depth`,
  `deepPath`, `buildFullDTree`, and `dtDepth`.
- `CircuitComplexity.PPoly`: the class `P/poly` of languages decided by
  polynomial-size non-uniform circuit families, over the `FeedForward` model.
- `CircuitComplexity.CircuitSat`: CKT-SAT ([AB09, Def 6.9]) and the Tseitin reduction
  to 3SAT ([AB09, Lem 6.11], equisatisfiability only), composed with
  `NPReductions.SATTo3SAT` to land in genuine 3-CNF.
- `CircuitComplexity.UnaryLanguages`: [AB09, Claim 6.8] — every unary
  language is in `P/poly`, via [AB09, Ex 6.3]'s AND circuit and a constant-`0`
  circuit built from the gate set.
- `CircuitComplexity.UHalt`: [AB09, p.110] — `UHALT`, an undecidable unary language,
  hence a language in `P/poly` that is not computable. `P ⊊ P/poly` itself is not
  stated: TCSlib has no `P`.
- `CircuitComplexity.Encoding`: a bit-string encoding of `BoolCircuit.Circuit` as a
  `Computability.FinEncoding`, CKT-SAT as a genuine `Language Bool`
  ([AB09, Def 6.9]), and the output-size half of [AB09, Lem 6.11] — clause count
  only, not `≤p`.
- `CircuitComplexity.Universal`: [AB09, Claim 2.13] — every Boolean function on
  `n` bits is computed by a circuit of size at most `2 ^ n * (n + 1) + 1`, via
  the DNF over its satisfying assignments.
- `CircuitComplexity.HardFunctions`: [AB09, Thm 6.21] — some Boolean function on
  `n` bits is computed by no circuit of size `2 ^ n / (n + 5)`, by counting.
- `CircuitComplexity.NCAC`: [AB09, Defs 6.24–6.25] — the classes `NC^d` / `AC^d`
  and their unions, and the inclusions `NC^i ⊆ AC^i ⊆ NC^{i+1}` and hence
  `NC = AC`. Over the tree-shaped `BoolCircuit.Circuit`, not the `FeedForward`
  model of `PPoly.lean`.
- `CircuitComplexity.Parity`: [AB09, Ex 6.26] — `PARITY ∈ NC¹`, by the balanced
  binary tree, built as dual pairs because `Circuit` negates only at literals.
- `CircuitComplexity.Hierarchy`: a nonuniform size hierarchy over the tree-shaped
  `BoolCircuit.Circuit`, from [AB09, Claim 2.13] and [AB09, Thm 6.21] by padding.
  **Not** [AB09, Thm 6.22]: its class is not `Language.InSIZE`.
- `CircuitComplexity.SizeClasses`: monotonicity of `SIZE`, the passage from
  `SIZE(T)` to `P/poly` for polynomially bounded `T`, and [AB09, Ex 6.3]
  — the all-ones language `{1ⁿ : n ∈ ℕ}` has linear-size circuits.

`Basic`, `Formulas` and `DecisionTree` are mutually independent; the bridge from
normal-form circuits to `DNF` / `CNF` lives in
`TCSlib.BooleanAnalysis.LMN.NormalFormConversion`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/
