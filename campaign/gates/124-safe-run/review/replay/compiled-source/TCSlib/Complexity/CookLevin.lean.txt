/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.CookLevin.Snapshot
import TCSlib.Complexity.CookLevin.Hardness

/-!
# Complexity — the Cook-Levin theorem

The Cook-Levin development of the Arora-Barak Chapter 2 campaign (see
`AroraBarakChapter2Plan.md`): computation is local over oblivious machines,
and `SAT`/`3SAT` are `NP`-complete.

## Contents

* `Snapshot` — snapshots, the input-length-indexed schedule, last visits, the
  finite reconstruction functions, and the locality theorems
  [AB09, §2.3.4].
* `Hardness` — Lemma 2.11 and Theorem 2.10: `SAT` and `3SAT` are
  `NP`-complete; hardness transfer along reductions [AB09, §2.2-2.3].
-/
