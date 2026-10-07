/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra.BadCount
import TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra.RootCube
import TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra.MultilinearSplit
import TCSlib.BooleanAnalysis.RazborovSmolensky.SmolenskyAlgebra.Counting

/-!
# The Smolensky side of Razborov–Smolensky

Facade for the low-degree inapproximability of `MOD q` over a field of
characteristic `p ≠ q`, via the root-of-unity cube.

## Contents

* `BadCount` — bad-input counts, averaging, and the reduction to circuit size.
* `RootCube` — the field `ModqField`, the cube `{1, ω}^n`, and squarefree polynomials.
* `MultilinearSplit` — splitting a multilinear polynomial at half degree.
* `Counting` — the counting obstruction for the top monomial.
-/
