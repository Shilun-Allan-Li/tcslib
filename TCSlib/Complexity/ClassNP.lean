/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.ClassNP.PolyTime
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.CoNP
import TCSlib.Complexity.ClassNP.EXP
import TCSlib.Complexity.ClassNP.Reductions
import TCSlib.Complexity.ClassNP.NTIME
import TCSlib.Complexity.ClassNP.Nondeterminism
import TCSlib.Complexity.ClassNP.SAT
import TCSlib.Complexity.ClassNP.TMSAT
import TCSlib.Complexity.ClassNP.Tautology

/-!
# Complexity — NP and NP-completeness

The classes and reduction notions of [AB09, ch. 2] (see
`AroraBarakChapter2Plan.md` for the chapter-level plan).

## Contents

* `PolyTime` — polynomial bounds and polynomial-time computable functions (FP),
  with the closure calculus reductions assemble with [AB09, §2.2].
* `NP` — the class `NP` via polynomial-time verifiers [AB09, Definition 2.1]
  and the bounded-length certificate variant [AB09, Exercise 2.1].
* `CoNP` — the class `coNP`, its ∀-certificate characterization
  [AB09, Definitions 2.19-2.20], and `P`'s closure under complement.
* `EXP` — the classes `EXP` and `NEXP` and the containment chain
  [AB09, Claim 2.4, §2.6.2].
* `Reductions` — Karp reductions, `NP`-hardness and `NP`-completeness
  [AB09, Definition 2.7, Theorem 2.8], and `HALT`'s status
  [AB09, Exercise 2.8].
* `NTIME` — nondeterministic deciding and the classes `NTIME`
  [AB09, §2.1.2, Definition 2.5] (the machine model lives in
  `TuringMachine/Nondeterministic`).
* `Nondeterminism` — the `NTIME` characterizations of `NP` [AB09, Theorem 2.6] and
  `NEXP` [AB09, §2.6.2], and the padding theorem [AB09, Theorem 2.22].
* `SAT` — the languages `SAT` and `3SAT`, their membership in `NP`, and
  `SAT ≤ₚ 3SAT` [AB09, §2.3.1, Theorem 2.10 (membership), Lemma 2.14] (the
  formula layer lives in `TCSlib.Complexity.Formulas`).
* `TMSAT` — the generic `NP`-complete language [AB09, Theorem 2.9], with the
  polynomial time-constructibility support statement.
* `Tautology` — `coNP`-hardness/completeness and `TAUTOLOGY` on the DNF
  fragment [AB09, §2.6.1, Example 2.21].
-/
