/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators

/-!
# Formula arithmetic

Shared combinators and arithmetic on `BoolCircuit.TreeCircuit` formulas: the circuit and formula
gadget layer of `machine-library-design.md` ("Circuit and formula gadgets").  New formulas are
assembled from it rather than built by hand.

## Contents

- `FormulaArith.Combinators`: the balanced binary gate `BoolCircuit.TreeCircuit.balanced` (fan-in
  two, `⌈log₂ |cs|⌉ + 1` extra depth), with its value, fan-in, depth and size lemmas.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
