/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Uncomputability.Computable
import TCSlib.Complexity.Uncomputability.Diagonalization
import TCSlib.Complexity.Uncomputability.Halting

/-!
# Complexity — Uncomputability

[AB09, §1.5]: not every function is computable. The diagonal function `UC` is
uncomputable by a direct diagonalization over machines-as-strings, and the halting
function `HALT` is uncomputable by reduction — the book's first reduction, run on
the universal machine (see `AroraBarakChapter1Plan.md`).

## Contents

* `Computable` — computable string functions, with no time bound
  [AB09, §1.4, p. 20].
* `Diagonalization` — the diagonal function `UC` and its uncomputability
  [AB09, Theorem 1.10], stated for every representation scheme.
* `Halting` — the halting function `HALT`, the reduction to `UC`, and
  [AB09, Theorem 1.11], stated for effective schemes.
-/
