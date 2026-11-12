/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.LowDegreeObstruction.SquarefreeRepresentative
import TCSlib.BooleanAnalysis.RazborovSmolensky.LowDegreeObstruction.Completeness
import TCSlib.BooleanAnalysis.RazborovSmolensky.LowDegreeObstruction.CountingObstruction

/-!
# The low-degree obstruction for the root-cube product

Facade for the concrete proof that `∏ i, x i` on `{1, ω}^n` has no low-degree
approximant, building on `TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra`.

## Contents

* `SquarefreeRepresentative` — low-degree squarefree polynomials and representatives.
* `Completeness` — degree-preserving multilinearization.
* `CountingObstruction` — the counting argument and the concrete lower bound.
-/
