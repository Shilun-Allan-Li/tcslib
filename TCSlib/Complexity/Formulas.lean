/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNF
import TCSlib.Complexity.Formulas.CNFEncoding

/-!
# Complexity — Boolean formulas

The formula layer of the Arora-Barak Chapter 2 development (see
`AroraBarakChapter2Plan.md`): CNF formulas over the Lean-core carrier
`Std.Sat.CNF ℕ`, and their binary serialization for the string languages
`SAT`/`3SAT` (in `TCSlib.Complexity.ClassNP`).

## Contents

* `CNF` — satisfiability, the variable-count measure, clause-width bounds, and
  CNF universality [AB09, §2.3.1, Claim 2.13], over `Std.Sat.CNF ℕ`.
* `CNFEncoding` — the unary-index LL(1) serialization, the exact-consumption
  parser, and the fixed-fallback totalization [AB09, §2.3.1, footnote 3].
-/
