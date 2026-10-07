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
import TCSlib.Complexity.CircuitComplexity.StraightLine
import TCSlib.Complexity.CircuitComplexity.StraightLineDualRail
import TCSlib.Complexity.CircuitComplexity.Adder
import TCSlib.Complexity.CircuitComplexity.AdderLanguage
import TCSlib.Complexity.CircuitComplexity.DAGHardFunctions
import TCSlib.Complexity.CircuitComplexity.HardWire
import TCSlib.Complexity.CircuitComplexity.Advice
import TCSlib.Complexity.CircuitComplexity.UnaryCode
import TCSlib.Complexity.CircuitComplexity.Uniform
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSat
import TCSlib.Complexity.CircuitComplexity.DAGCircuitSatLang
import TCSlib.Complexity.CircuitComplexity.CircuitEvalSpec
import TCSlib.Complexity.CircuitComplexity.CircuitEvalCorrect
import TCSlib.Complexity.CircuitComplexity.CircuitEvalMachine
import TCSlib.Complexity.CircuitComplexity.CircuitEvalRun
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.CircuitComplexity.CircuitEvalNP
import TCSlib.Complexity.CircuitComplexity.PUniformP
import TCSlib.Complexity.CircuitComplexity.PPolyAdvice
import TCSlib.Complexity.CircuitComplexity.UHaltMachine
import TCSlib.Complexity.CircuitComplexity.CircuitSatReduction
import TCSlib.Complexity.CircuitComplexity.BookModelBasics
import TCSlib.Complexity.CircuitComplexity.LupanovGates
import TCSlib.Complexity.CircuitComplexity.Lupanov
import TCSlib.Complexity.CircuitComplexity.FanOut
import TCSlib.Complexity.CircuitComplexity.FormulaFanOut
import TCSlib.Complexity.CircuitComplexity.StrictCircuit
import TCSlib.Complexity.CircuitComplexity.StrictSize
import TCSlib.Complexity.CircuitComplexity.StrictFanOut
import TCSlib.Complexity.CircuitComplexity.SequentialCircuit
import TCSlib.Complexity.CircuitComplexity.ShannonProbabilistic
import TCSlib.Complexity.CircuitComplexity.StraightLineSmall
import TCSlib.Complexity.CircuitComplexity.KarpLiptonSearch
import TCSlib.Complexity.CircuitComplexity.KarpLipton
import TCSlib.Complexity.CircuitComplexity.KarpLiptonSearchFamily
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyGadget
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyTableau
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyTableauCorrect
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyProgram
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyConfigStep
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyConfig
import TCSlib.Complexity.CircuitComplexity.PSubsetPPolyConfigCircuit
import TCSlib.Complexity.CircuitComplexity.PSubsetPPoly
import TCSlib.Complexity.CircuitComplexity.PAdviceSubsetPPoly
import TCSlib.Complexity.CircuitComplexity.UniformTableau
import TCSlib.Complexity.CircuitComplexity.CircuitSatNPHard
import TCSlib.Complexity.CircuitComplexity.LogspaceUniform
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdjBasic
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformScan
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformWalk
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdj
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformCanon
import TCSlib.Complexity.CircuitComplexity.LogspaceTableau
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformExample
import TCSlib.Complexity.CircuitComplexity.Meyer
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionMachine
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionMachineTapes
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionSpec
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionValid
import TCSlib.Complexity.CircuitComplexity.KarpLiptonPrefix
import TCSlib.Complexity.CircuitComplexity.LogspaceTableauFront
import TCSlib.Complexity.CircuitComplexity.MeyerComplete
import TCSlib.Complexity.CircuitComplexity.MeyerMachine
import TCSlib.Complexity.CircuitComplexity.MeyerMachineParse
import TCSlib.Complexity.CircuitComplexity.MeyerMachineRun
import TCSlib.Complexity.CircuitComplexity.MeyerMachineSetup
import TCSlib.Complexity.CircuitComplexity.MeyerMachineWalk
import TCSlib.Complexity.CircuitComplexity.MeyerSigma
import TCSlib.Complexity.CircuitComplexity.MeyerSigmaEXP
import TCSlib.Complexity.CircuitComplexity.MeyerSound
import TCSlib.Complexity.CircuitComplexity.MeyerSoundInput
import TCSlib.Complexity.CircuitComplexity.MeyerTab
import TCSlib.Complexity.CircuitComplexity.MeyerTableau
import TCSlib.Complexity.CircuitComplexity.MeyerVerifier
import TCSlib.Complexity.CircuitComplexity.MeyerVerifierGlue
import TCSlib.Complexity.CircuitComplexity.UniformTableauCircuit
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitter
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitterInstr
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitterLayer
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitterMain
import TCSlib.Complexity.CircuitComplexity.UniformTableauEmitterSteps
import TCSlib.Complexity.CircuitComplexity.UniformTableauSpec

/-!
# Circuit Complexity

Boolean circuits and formulas, the class `P/poly`, and Arora–Barak §§6.1–6.3
(with §6.5 and §6.7).

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
  families, with the shared gate-level toolkit: acyclic gate lists (`GatesAcyclic`), gate
  predicates (`DAGGate.WellFormed`, `DAGGate.FaninTwo`), constant gates and circuits
  (`constGate`, `constCircuit`), and vertex renaming (`DAGGate.remap`,
  `runWith_remap_rel`).
- `CircuitComplexity.PPoly`: `SIZE(T)` and `P/poly` [AB09, Defs 6.2, 6.5] over DAG circuits;
  the literal `⋃_c SIZE(n^c)` is empty, and `P/poly` is `|C_n| ≤ n^c` for `n ≥ 2`.
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
- `CircuitComplexity.CircuitSat`: CKT-SAT ([AB09, Def 6.9]) over tree circuits and the
  Tseitin reduction to 3SAT (equisatisfiability), composed with `NPReductions.SATTo3SAT`
  to land in genuine 3-CNF.  The book's [AB09, Lem 6.11], with `≤ₚ`, is over the DAG
  model in `CircuitComplexity.CircuitSatReduction`.
- `CircuitComplexity.UnaryLanguages`: [AB09, Claim 6.8] — every unary
  language is in `P/poly`, via [AB09, Ex 6.3]'s AND circuit and a constant-`0`
  circuit built from the layered gate set, then transferred to the book's `P/poly`.
- `CircuitComplexity.UHalt`: [AB09, p.110] — `UHALT`, an undecidable unary language,
  hence a language in `P/poly` that is not computable (Mathlib's `ComputablePred`). The
  machine-model version and `P ⊊ P/poly` are `CircuitComplexity.UHaltMachine` and
  `Complexity.P_ssubset_PPoly`.
- `CircuitComplexity.Encoding`: a bit-string encoding of `BoolCircuit.TreeCircuit` as a
  `Computability.FinEncoding`, CKT-SAT as a genuine `Language Bool`
  ([AB09, Def 6.9]), and a clause-count bound for the tree-circuit Tseitin reduction (the
  `≤ₚ` statement of [AB09, Lem 6.11] is the DAG-model `CircuitSatReduction`).
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
  [AB09, Ex 6.3] — the all-ones language `{1ⁿ : n ∈ ℕ}` has linear-size layered circuits
  (the book-model version, and `{1ⁿ} ∈ P/poly`, are in `BookModelBasics`).

- `CircuitComplexity.StraightLine` / `StraightLineDualRail`: [AB09, Note 6.4] Boolean
  straight-line programs, the XOR circuit of [AB09, Fig 6.1], and [AB09, Ex 6.2]'s
  equivalence with DAG circuits, with explicit constants (program → circuit of size
  `2n + max S 1`; circuit → program of `2(S − n) + 1` lines by dual rail, `n ≥ 1`).
- `CircuitComplexity.Adder` / `AdderLanguage`: the second half of [AB09, Ex 6.3] — a
  ripple-carry adder; the addition language `{⟨m, n, m + n⟩}` is in `SIZE(6n + 4)`.
- `CircuitComplexity.DAGHardFunctions`: [AB09, Thm 6.21] over the book's DAG model, with the
  book's bound — for `n > 1` some `f` on `n` bits has no circuit of size `2 ^ n / (10 n)`.
- `CircuitComplexity.HardWire`: the hard-wiring construction of [AB09, Thm 6.18]'s proof —
  fixing some inputs of a circuit preserves its size — and the `P/poly` corollary for
  hard-wired advice.
- `CircuitComplexity.Advice`: [AB09, Def 6.16] `DTIME(T)/a` (machine reads the
  self-delimiting pair `⟨x, αₙ⟩`), the class `⋃ DTIME(n^c)/n^d` of [AB09, Thm 6.18],
  `DTIME(T)/0 = DTIME(T)` (for `T(n) ≥ n + 1`) and `⋃_c DTIME(n^c + 1)/0 = P`, `P ⊆`
  `⋃ DTIME(n^c)/n^d`, and [AB09, Ex 6.17] — unary languages are in `DTIME(n)/1`.
- `CircuitComplexity.UnaryCode`: the unary number code `1ᵏ0` (`encodeNat` / `decodeNat`)
  shared by the circuit descriptions of `Encoding` and `Uniform`.
- `CircuitComplexity.Uniform`: an injective bit encoding of DAG circuits and [AB09, Def 6.12]
  P-uniform circuit families (logspace uniformity, Def 6.14, is `LogspaceUniform` below).
- `CircuitComplexity.DAGCircuitSat` / `DAGCircuitSatLang`: [AB09, Def 6.9] CKT-SAT and the
  Tseitin construction of [AB09, Lem 6.11] over the book's DAG model — one variable per
  vertex, a genuine 3-CNF, equisatisfiable — and the string-level many-one map into
  `Complexity.SAT3`.
- `CircuitComplexity.CircuitSatReduction` (with `…Valid` / `…Spec` / `…Machine` /
  `…MachineTapes`, and the one-pass transducers of `ClassNP.Transducer`): [AB09, Lem 6.11]
  in full — the Tseitin map is polynomial-time computable, so `CKT-SAT ≤ₚ 3SAT`
  (`dagCktSatLang_polyTimeReducible_SAT3`).
- `CircuitComplexity.CircuitEval` (with `CircuitEvalSpec` / `Correct` / `Machine` / `Run`):
  circuit evaluation is in `P` — a two-work-tape binary machine decides
  `CVAL = {⟨C, x⟩ : C(x) = 1}` in time `12 (m + 1)²` — the fact [AB09] uses in the proofs
  of Thms 6.13, 6.18 and 6.19.
- `CircuitComplexity.CircuitEvalNP`: CKT-SAT (`dagCktSatLang`) is in `NP` ([AB09, p. 111]).
- `CircuitComplexity.PUniformP`: the "if" direction of [AB09, Thm 6.13] — a language
  decided by a P-uniform fan-in-two family is in `P`.
- `CircuitComplexity.PPolyAdvice`: the `⊆` direction of [AB09, Thm 6.18] —
  `P/poly ⊆ ⋃ DTIME(n^c)/n^d`, with the padded circuit description as advice.

- `CircuitComplexity.UHaltMachine`: [AB09, p. 110] `UHALT` over the library's own machine
  model and `Complexity.HALT` — undecidable by any machine, hence outside `EXP` and `P`, yet
  in `P/poly`; with `P ⊆ P/poly` it gives `P ⊊ P/poly`. (`UHalt.lean` is the counterpart
  stated with Mathlib's `ComputablePred`.)

- `CircuitComplexity.BookModelBasics`: book-model facts of [AB09, pp. 107–108] — `{1ⁿ}` in
  `SIZE(2n + 1)` ([AB09, Ex 6.3]), a fan-in-`f` gate costs `f − 1` fan-in-two gates, and
  [AB09, Claim 2.13] as fan-in-two DAG circuits of size `n2ⁿ + 2n + 1`.
- `CircuitComplexity.Lupanov` (with `LupanovGates`): [AB09, p. 108, Ex 6.1] — every
  `f : {0,1}ⁿ → {0,1}` has a fan-in-two DAG circuit with `(n + 1) · size ≤ 40 · 2ⁿ`, i.e.
  size `O(2ⁿ/n)` (all functions of the last `≈ log₂ n - 1` inputs, shared, combined with
  the minterms of the rest); hence every language is in `SIZE(40 · 2ⁿ / (n + 1))`.
- `CircuitComplexity.FanOut`: fan-out two suffices ([AB09, p. 108]) — size at most `3S`.
- `CircuitComplexity.FormulaFanOut`: formulas are the fan-out-one circuits ([AB09, p. 108]) —
  a compiled formula's gates have fan-out one, and a fan-in-two circuit whose gates have
  fan-out at most one unfolds to a formula with at most `3 · #gates + 1` nodes.
- `CircuitComplexity.StrictCircuit` (with `StrictSize` / `StrictFanOut`): [AB09, Def 6.1]
  taken literally (`DAGCircuit.IsStrict`: `∧`/`∨` fan-in exactly two, `¬` fan-in one, the
  output the only sink).  No strict circuit has `0` inputs.  For `n ≥ 1` every fan-in-two
  circuit of size `S` has a strict equivalent of size `≤ 4S + 12`, so `P/poly` is unchanged
  (`Language.inPPoly_iff_inStrictPPoly`).  Fan-out two with `¬¬` buffers costs `5S`, and
  `20S` within the literal model.
- `CircuitComplexity.SequentialCircuit`: [AB09, p. 108, footnote 1] — a synchronous sequential
  circuit with `C` gates and registers run for `T` ticks unrolls to a circuit of size
  `≤ 2(C·T + n)`.
- `CircuitComplexity.ShannonProbabilistic`: the probabilistic form of [AB09, Thm 6.21]
  (p. 115) — a uniformly random `f` has a circuit of size `2ⁿ/(10n)` with probability at most
  `2^(−2ⁿ/10)`, via the book's steps: `Pr[C(x) = f(x)] = 1/2`, `Pr[C computes f] = 2^{-2ⁿ}`,
  and the union bound over the circuits.
- `CircuitComplexity.StraightLineSmall`: exact `S`-line programs from size-`S` circuits for
  `n ≤ 2` (sharpening of [AB09, Note 6.4]).
- `CircuitComplexity.KarpLipton` (with `KarpLiptonPrefix` / `KarpLiptonSearch` /
  `KarpLiptonSearchFamily`): [AB09, Thm 6.19] Karp–Lipton — `NP ⊆ P/poly → PH = Σ₂ᵖ` — with multi-output circuits and the
  search-to-decision circuit `C′ₙ` of its proof.

- `CircuitComplexity.PSubsetPPoly` (with `PSubsetPPolyGadget` / `Tableau` / `TableauCorrect` /
  `Program`): [AB09, Thm 6.6] `P ⊆ P/poly`, via the oblivious snapshot tableau of the proof —
  one constant-size gadget per step, wired by the oblivious schedule — and hence
  `P ⊊ P/poly` ([AB09, p. 110]) and `NP ⊄ P/poly → P ≠ NP` ([AB09, p. 115]).
- `CircuitComplexity.PAdviceSubsetPPoly` (with `PSubsetPPolyConfigStep` / `Config` /
  `ConfigCircuit`): the `⊇` direction of [AB09, Thm 6.18], via a configuration tableau for
  machines correct only on `⟨x, αₙ⟩` and hard-wired advice; hence
  `P/poly = ⋃ DTIME(n^c)/n^d`, also with the book's advice length `n^d` exactly
  (`PPoly_eq_iUnion_DTIMEAdvice_pow`; the time `n^c + 1` is forced, as the literal
  `DTIME(n^c)/a` is empty for `c ≥ 1`), and `UHALT` with one advice bit ([AB09, Ex 6.17]).

- `CircuitComplexity.UniformTableau` (with `UniformTableauCircuit` / `Spec` / `Emitter*`, and
  the counter programs of `TuringMachine.CounterProg*`): the uniform version of [AB09, Thm
  6.6] — a polynomial-time machine prints the tableau circuit from `1ⁿ` ([AB09, Remark 6.7],
  polynomial-time half) — hence [AB09, Thm 6.13] in full: `L ∈ P` iff `L` has P-uniform
  circuits.
- `CircuitComplexity.CircuitSatNPHard`: [AB09, Lem 6.10] CKT-SAT is `NP`-hard (so
  `NP`-complete), and with Lem 6.11 the Cook–Levin theorem ([AB09, p. 111, Thm 2.10]):
  `3SAT` is `NP`-hard (`Complexity.SAT3_NPHard_viaCircuits`, the book's alternative proof; the
  canonical Cook–Levin theorems are in `CookLevin/Hardness.lean`).

- `CircuitComplexity.LogspaceUniform` (with `…AdjBasic` / `…Scan` / `…Walk` / `…Adj` /
  `…Canon` / `…Example`): [AB09, Def 6.14] logspace-uniform families (over
  `Complexity.ImplicitlyLogspaceComputable`, [AB09, Def 4.16], in `SpaceComplexity`),
  logspace-uniform ⇒ P-uniform, and the p. 112 robustness remark — logspace-uniformity is
  equivalent to `SIZE`/`TYPE`/`EDGE` being logspace computable (for circuits in the book's
  normal form; any family has a canonical equivalent).
- `CircuitComplexity.LogspaceTableau` (with `…Front`, and the generic logspace material of
  `SpaceComplexity.UnaryLogspace` / `CounterProgSim*` / `Machines.DblLang`): [AB09, Thm 6.15]
  `L ∈ P` iff `L` has polynomial-size logspace-uniform circuits, and the logspace half of
  [AB09, Remark 6.7].

- `CircuitComplexity.Meyer` (with `MeyerMachine*` / `MeyerTab` / `MeyerTableau` /
  `MeyerVerifier*` / `MeyerSound*` / `MeyerComplete` / `MeyerSigma*`): [AB09, Thm 6.20]
  Meyer's theorem — `EXP ⊆ P/poly → EXP = Σ₂ᵖ` (with `Σ₂ᵖ ⊆ EXP` unconditionally) — and the
  p. 115 corollary `P = NP → EXP ⊄ P/poly`, via the time hierarchy theorem.

`Basic` and `Formulas` are mutually independent (decision trees are
`TCSlib.BooleanAnalysis.DecisionTree`); the bridge from normal-form circuits to `DNF` /
`CNF` lives in `TCSlib.BooleanAnalysis.LMN.NormalFormConversion`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/
