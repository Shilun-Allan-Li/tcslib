/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.BooleanAnalysis.DecisionTree
import TCSlib.Complexity.CircuitComplexity.Basic
import TCSlib.Complexity.CircuitComplexity.FeedForward
import TCSlib.Complexity.CircuitComplexity.Formulas
import TCSlib.Complexity.CircuitComplexity.NCAC
import TCSlib.Complexity.CircuitComplexity.PPoly
import TCSlib.Complexity.Formulas.CNF
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

* `BoolCircuit.Circuit n` — tree-shaped Boolean circuits: unbounded fan-in
  AND/OR nodes over polarity-carrying literals
  (`Complexity/CircuitComplexity/Basic.lean`).
* `BoolCircuit.CircuitFamily` — non-uniform families of `FeedForward`
  circuits, one per input length; the carrier of `Language.InSIZE` and
  `P/poly` (`Complexity/CircuitComplexity/PPoly.lean`).
* `BoolCircuit.FeedForward α inp out` — layered DAG circuits over an
  arbitrary alphabet, with the `stdGateOps` basis
  (`Complexity/CircuitComplexity/FeedForward.lean`).
* `BoolCircuit.TreeCircuitFamily` — non-uniform families of tree circuits;
  the carrier of `NC` and `AC` (`Complexity/CircuitComplexity/NCAC.lean`).
* `CNF n` / `DNF n`, over `Literal n` and `Term n` — flat width-measured
  formulas for the switching-lemma development [OD14]
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

## Conversions

Model-to-model maps (pointers only — their files are not imported here):

* `BoolCircuit.Circuit.toFeedForward` — tree → DAG, faithful embedding with
  identity-wire padding (`Complexity/CircuitComplexity/FeedForward.lean`).
* `BoolCircuit.Circuit.tseitin` / `Circuit.toCNF` — circuits →
  equisatisfiable `NPReductions.CNFFormula`
  (`Complexity/CircuitComplexity/CircuitSat.lean`).
* `BoolCircuit.FeedForward.toCircuit` — DAG → tree unrolling, exponential
  in depth (`Complexity/CircuitComplexity/FeedForward.lean`).
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
