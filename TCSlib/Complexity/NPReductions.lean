import TCSlib.Complexity.NPReductions.SATTo3SAT
import TCSlib.Complexity.NPReductions.ThreeSATToClique
import TCSlib.Complexity.NPReductions.NAESATToColoring
import TCSlib.Complexity.NPReductions.ThreeSATToColoring

/-
Copyright (c) 2026 Yangshuo Zou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yangshuo Zou
-/

/-!
# NP-Completeness Reductions

This module collects polynomial-time reductions between NP-complete problems,
formalised in Lean 4 using Mathlib.

## Contents

- `NPReductions.SATTo3SAT`: SAT → 3-SAT (chain encoding, equisatisfiability)
- `NPReductions.ThreeSATToClique`: 3-SAT → Clique (conflict graph construction)
- `NPReductions.NAESATToColoring`: NAE-SAT → 3-Coloring (variable/clause gadget)
- `NPReductions.ThreeSATToColoring`: 3-SAT → 3-Coloring (palette + clause gadget)
-/
