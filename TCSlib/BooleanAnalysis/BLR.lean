import TCSlib.BooleanAnalysis.BLR.BoolFourier
import TCSlib.BooleanAnalysis.BLR.BoolBLR
import TCSlib.BooleanAnalysis.BLR.ZkFourier
import TCSlib.BooleanAnalysis.BLR.ZkBLR
import TCSlib.BooleanAnalysis.BLR.LowDegree

/-
Copyright (c) 2026 Prastik Mohanraj. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Prastik Mohanraj
-/

set_option maxHeartbeats 0

/-!
# BooleanAnalysis.BLR

This module collects the BLR (Blum-Luby-Rubinfeld) linearity testing results,
including Fourier analysis on Boolean and ℤ_k^n domains, and low-degree testing.

## Sub-modules

- `TCSlib.BooleanAnalysis.BLR.BoolFourier`: Fourier analysis on the Boolean hypercube
  (`{±1}`-valued characters, orthogonality, Parseval's identity).
- `TCSlib.BooleanAnalysis.BLR.BoolBLR`: BLR linearity test on the Boolean hypercube
  (completeness, soundness via Fourier coefficients).
- `TCSlib.BooleanAnalysis.BLR.ZkFourier`: Fourier analysis on ℤ_k^n
  (roots of unity, character orthogonality, Parseval's identity over ℤ_k).
- `TCSlib.BooleanAnalysis.BLR.ZkBLR`: BLR linearity test on ℤ_k^n
  (completeness, soundness for prime fields).
- `TCSlib.BooleanAnalysis.BLR.LowDegree`: Low-degree (Reed-Muller) testing on the Boolean hypercube
  (Gowers norms, degree test completeness and soundness).
-/
