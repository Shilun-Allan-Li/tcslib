/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.BooleanAnalysis.DecisionTree
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.CircuitComplexity.DAGCircuit
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.CircuitComplexity.LayeredCircuit
import TCSlib.Complexity.CircuitComplexity.Formulas
import TCSlib.Complexity.CircuitComplexity.TreeNCAC
import TCSlib.Complexity.CircuitComplexity.LayeredPPoly
import TCSlib.Complexity.Formulas.CNF
import TCSlib.Complexity.Formulas.DNF
import TCSlib.Complexity.NPReductions.SATTo3SAT
import TCSlib.Complexity.TuringMachine.Deterministic
import TCSlib.Complexity.TuringMachine.Finite
import TCSlib.Complexity.TuringMachine.Nondeterministic
import TCSlib.Complexity.TuringMachine.Oracle

/-!
# Computational models: the catalog

Every model of computation in TCSlib, in one place. This facade imports each
model's defining file, so the catalog cannot silently rot: if a defining file
moves, this module stops compiling. `policy.md` §1 licenses a root-level
model *type* only when it is registered here; the model's operations and
lemmas still live in its own namespace.

Entries are alphabetical. Paths are relative to `TCSlib/`; machine files live
under `Complexity/`.

## Models

* `BoolCircuit.DAGCircuit n` — the book's Boolean circuits [AB09, Def 6.1]:
  topologically numbered DAGs of `∧`/`∨`/`¬` gates, size counting every vertex
  (`Complexity/CircuitComplexity/DAGCircuit.lean`).
* `BoolCircuit.DAGCircuitFamily` — non-uniform families of `DAGCircuit`s; the
  carrier of the book's `SIZE`, `P/poly`, `NC`, `AC`
  (`Complexity/CircuitComplexity/PPoly.lean`, `NCAC.lean`).
* `BoolCircuit.TreeCircuit n` — tree-shaped Boolean circuits (formulas):
  unbounded fan-in AND/OR nodes over polarity-carrying literals
  (`Complexity/CircuitComplexity/Basic.lean`).
* `BoolCircuit.LayeredCircuitFamily` — non-uniform families of `LayeredCircuit`
  circuits, one per input length; the carrier of `Language.InLayeredSIZE` and
  `P/poly` (`Complexity/CircuitComplexity/LayeredPPoly.lean`).
* `BoolCircuit.LayeredCircuit α inp out` — layered DAG circuits over an
  arbitrary alphabet; the raw model enforces no gate basis, and classes impose
  `stdGateOps` via `OnlyUsesGates`
  (`Complexity/CircuitComplexity/LayeredCircuit.lean`).
* `BoolCircuit.TreeCircuitFamily` — non-uniform families of tree circuits;
  the carrier of the formula classes `TreeNC` and `TreeAC`
  (`Complexity/CircuitComplexity/TreeNCAC.lean`).
* `CNF n` / `DNF n` — the two readings (AND of clauses / OR of terms) of a
  reading-neutral `Depth2 n` shape of `LitList n`s over `Literal n`; flat
  width-measured formulas for the switching-lemma development [OD14]
  (`Complexity/CircuitComplexity/Formulas.lean`).
* `DecisionTree n` — binary decision trees, with `dtDepth` the least depth
  computing a given function [OD14] (`BooleanAnalysis/DecisionTree.lean`).
* `FinNDTM` — bundled binary-choice nondeterministic machines; the carrier
  of `NTIME`, `NP`, `NEXP` (`Complexity/TuringMachine/Nondeterministic.lean`).
* `FinTM` — bundled deterministic machines; the carrier of `DTIME`, `P`,
  `EXP` (`Complexity/TuringMachine/Finite.lean`).
* `MultiTapeTM k Symbol State` — k-tape deterministic Turing machines with
  append-only output, the raw layer under `FinTM`
  (`Complexity/TuringMachine/Deterministic.lean`).
* `NDTM k Symbol State` — the raw layer under `FinNDTM`: binary-choice
  transitions, `List Bool` choice words
  (`Complexity/TuringMachine/Nondeterministic.lean`).
* `NPReductions.CNFFormula V` — the legacy variable-indexed CNF used by the
  SAT→3SAT reduction and the Tseitin encoding
  (`Complexity/NPReductions/SATTo3SAT.lean`).
* `OracleTM k Symbol State` — oracle machines with a dedicated query tape
  and one-step answers (`Complexity/TuringMachine/Oracle.lean`).
* `Std.Sat.CNF ℕ` — Lean core's clause-list CNF, the campaign's SAT/3SAT
  carrier; TCSlib's layer over it is in `Complexity/Formulas/CNF.lean`,
  with serialization in `Complexity/Formulas/CNFEncoding.lean`.
* `Std.Sat.DNF` — the same list-of-literal-lists shape read as an OR of ANDs,
  in its own type; the TAUTOLOGY carrier (`Complexity/Formulas/DNF.lean`).

## Conversions

Model-to-model maps (pointers only — their files are not imported here):

* `BoolCircuit.TreeCircuit.toDAG` / `BoolCircuit.DAGCircuit.toTree` — formulas → DAGs
  (linear) and DAGs → formulas (exponential in depth)
  (`Complexity/CircuitComplexity/TreeDAG.lean`).
* `BoolCircuit.DAGCircuit.toLayered` / `BoolCircuit.LayeredCircuit.toDAG` — DAGs ↔ layered
  circuits over `stdGateOps`, polynomial both ways; `BoolCircuit.TreeCircuit.toLayered` —
  formulas → layered circuits, gate by gate
  (`Complexity/CircuitComplexity/LayeredDAG.lean`).
* `BoolCircuit.DAGCircuit.binarize` / `BoolCircuit.DAGCircuit.deMorgan` — fan-in reduction
  and `∨`-elimination on DAGs (`Complexity/CircuitComplexity/DAGFanin.lean`).
* `BoolCircuit.TreeCircuit.toLayeredWrapper` — a semantic wrapper, not an embedding:
  the tree's evaluation becomes a single unrestricted first-layer gate, so only
  evaluation is preserved, with no general gate-basis guarantee
  (`Complexity/CircuitComplexity/LayeredCircuit.lean`).
* `BoolCircuit.TreeCircuit.tseitin` / `TreeCircuit.toCNF` — circuits →
  equisatisfiable `NPReductions.CNFFormula`
  (`Complexity/CircuitComplexity/CircuitSat.lean`).
* `BoolCircuit.LayeredCircuit.toTreeCircuit` — DAG → tree unrolling, exponential
  in depth (`Complexity/CircuitComplexity/LayeredCircuit.lean`).
* `FinTM.toFinNDTM` — deterministic machines as nondeterministic ones, in
  lockstep (`Complexity/TuringMachine/Nondeterministic.lean`).
* `LMN.NormalFormConversion` — normal-form tree circuits ↔ `CNF`/`DNF`
  formulas (`BooleanAnalysis/LMN/NormalFormConversion.lean`).
* `MultiTapeTM.toNDTM` — the raw-layer deterministic → nondeterministic
  embedding (`Complexity/TuringMachine/Nondeterministic.lean`).
* `OracleTM.ofMultiTapeTM` — plain machines as oracle machines that never
  query (`Complexity/TuringMachine/Oracle.lean`).

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
* [OD14] R. O'Donnell, *Analysis of Boolean Functions*, Cambridge University
  Press, 2014.
-/
