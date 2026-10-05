/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang, Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.CircuitComplexity.Formulas
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.CircuitComplexity.NCAC
import TCSlib.Complexity.CircuitComplexity.TreeDAG
import TCSlib.Complexity.CircuitComplexity.DAGTransform
import TCSlib.Complexity.CircuitComplexity.DAGFanin
import TCSlib.Complexity.CircuitComplexity.LayeredCircuit
import TCSlib.Complexity.CircuitComplexity.LayeredPPoly
import TCSlib.Complexity.CircuitComplexity.LayeredDAG
import TCSlib.Complexity.CircuitComplexity.CircuitSat
import TCSlib.Complexity.CircuitComplexity.Encoding
import TCSlib.Complexity.CircuitComplexity.Universal
import TCSlib.Complexity.CircuitComplexity.HardFunctions
import TCSlib.Complexity.CircuitComplexity.TreeNCAC
import TCSlib.Complexity.CircuitComplexity.Parity
import TCSlib.Complexity.CircuitComplexity.Hierarchy
import TCSlib.Complexity.CircuitComplexity.UnaryLanguages
import TCSlib.Complexity.CircuitComplexity.UHalt
import TCSlib.Complexity.CircuitComplexity.SizeClasses

/-!
# Circuit Complexity

Boolean circuits and formulas, the class `P/poly`, and Arora–Barak §6.1.

## Circuit models

Three models, with conversions between them:

* `BoolCircuit.DAGCircuit` — **the book's model** ([AB09, Def 6.1]): DAGs with `∧`/`∨`/`¬`
  gates, size counting every vertex.  The book's classes `SIZE`, `P/poly`, `NC`, `AC` are
  stated over it (`Language.InSIZE`, `Language.InPPoly`, `Language.InNC`, `Language.InAC`).
* `BoolCircuit.TreeCircuit` — formulas: fan-out one, unbounded fan-in, negation only at
  the inputs.  The model of the switching lemma / LMN development and of the formula
  classes `Language.InTreeSize`, `Language.InTreeNC`, `Language.InTreeAC`.
* `BoolCircuit.LayeredCircuit` — layered DAGs over an arbitrary gate set; the carrier of the
  Razborov–Smolensky development and of `Language.InLayeredSIZE` / `Language.InLayeredPPoly`.

Tree ↔ DAG is `TreeDAG.lean` (linear one way, depth-exponential the other; the formula and
circuit classes agree at `NC¹` and `AC⁰`), Layered ↔ DAG is `LayeredDAG.lean` (polynomial
both ways, so the two `P/poly`s coincide).

## Contents

- `CircuitComplexity.Basic`: `BoolCircuit.Lit`, the general circuit tree
  `BoolCircuit.TreeCircuit` (unbounded fan-in) with `eval` / `litCount` / `depth` /
  `size` / `maxFanin`, and the alternating normal forms
  `NAndCircuit` / `NOrCircuit` with `toNAnd` / `toNOr` and the forgetful map
  `toTreeCircuit`.
- `CircuitComplexity.Formulas`: `Literal`, `Term`, `DNF`, `CNF` with `eval`
  and `width`.
- `CircuitComplexity.DAGCircuit`: the book's circuit model [AB09, Def 6.1] and circuit
  families.
- `CircuitComplexity.PPoly`: `SIZE(T)` and `P/poly` [AB09, Defs 6.2, 6.5] over DAG circuits.
- `CircuitComplexity.NCAC`: `NC^d`, `AC^d` [AB09, Defs 6.24, 6.25] over DAG circuits,
  `NC^i ⊆ AC^i ⊆ NC^{i+1}`, `NC = AC`, `NC ⊆ P/poly`, and the comparison with the formula
  classes (equal at `NC¹` and `AC⁰`).
- `CircuitComplexity.TreeDAG`: tree ↔ DAG conversions.
- `CircuitComplexity.DAGTransform` / `DAGFanin`: a generic gate-rewriting pass on DAGs, and
  its instances binarization (fan-in two, [AB09, p. 118]) and De Morgan normalization.
- `CircuitComplexity.LayeredCircuit`: the layered model and its gate set `stdGateOps`.
- `CircuitComplexity.LayeredPPoly`: `SIZE` and `P/poly` over the layered model.
- `CircuitComplexity.LayeredDAG`: layered ↔ DAG conversions, and
  `Language.inPPoly_iff_inLayeredPPoly`.
- `CircuitComplexity.CircuitSat`: CKT-SAT ([AB09, Def 6.9]) and the Tseitin reduction
  to 3SAT ([AB09, Lem 6.11], equisatisfiability only), composed with
  `NPReductions.SATTo3SAT` to land in genuine 3-CNF.
- `CircuitComplexity.UnaryLanguages`: [AB09, Claim 6.8] — every unary
  language is in `P/poly`, via [AB09, Ex 6.3]'s AND circuit and a constant-`0`
  circuit built from the layered gate set, then transferred to the book's `P/poly`.
- `CircuitComplexity.UHalt`: [AB09, p.110] — `UHALT`, an undecidable unary language,
  hence a language in `P/poly` that is not computable. `P ⊊ P/poly` itself is not
  stated: the bridge from the campaign's `P` to `P/poly` ([AB09, Thm 6.6]) and
  the computability-framework bridge are both deferred (`backlog.md` §3).
- `CircuitComplexity.Encoding`: a bit-string encoding of `BoolCircuit.TreeCircuit` as a
  `Computability.FinEncoding`, CKT-SAT as a genuine `Language Bool`
  ([AB09, Def 6.9]), and the output-size half of [AB09, Lem 6.11] — clause count
  only, not `≤p`.
- `CircuitComplexity.Universal`: [AB09, Claim 2.13] — every Boolean function on
  `n` bits is computed by a circuit of size at most `2 ^ n * (n + 1) + 1`, via
  the DNF over its satisfying assignments.
- `CircuitComplexity.HardFunctions`: the tree-circuit analogue of [AB09, Thm 6.21]
  — some Boolean function on `n` bits is computed by no **tree** circuit of size
  `2 ^ n / (n + 5)`, by counting over the tree encoding.
- `CircuitComplexity.TreeNCAC`: the formula versions of [AB09, Defs 6.24–6.25] —
  `NC^d` / `AC^d` over `BoolCircuit.TreeCircuit` — with `NC^i ⊆ AC^i ⊆ NC^{i+1}` and
  `TreeNC = TreeAC`.
- `CircuitComplexity.Parity`: [AB09, Ex 6.26] — `PARITY ∈ NC¹`, by the balanced
  binary tree, built as dual pairs because `TreeCircuit` negates only at literals, then
  compiled to the book's `NC¹`.
- `CircuitComplexity.Hierarchy`: a nonuniform size hierarchy over the tree-shaped
  `BoolCircuit.TreeCircuit`, from [AB09, Claim 2.13] and [AB09, Thm 6.21] by padding.
  **Not** [AB09, Thm 6.22]: its class is the formula class `Language.InTreeSize`; formula
  size does bound circuit size (`Language.InTreeSize.inSIZE`), so the upper half transfers.
- `CircuitComplexity.SizeClasses`: monotonicity of the layered size classes
  (`Language.InLayeredSIZE`), the passage to `P/poly` for polynomially bounded budgets, and
  [AB09, Ex 6.3] — the all-ones language `{1ⁿ : n ∈ ℕ}` has linear-size circuits, hence is
  in the book's `P/poly`.

`Basic`, `Formulas` and `DecisionTree` are mutually independent; the bridge from
normal-form circuits to `DNF` / `CNF` lives in
`TCSlib.BooleanAnalysis.LMN.NormalFormConversion`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/
