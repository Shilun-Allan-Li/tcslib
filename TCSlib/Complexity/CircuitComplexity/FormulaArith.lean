/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Combinators
import TCSlib.Complexity.CircuitComplexity.FormulaArith.CarrySave
import TCSlib.Complexity.CircuitComplexity.FormulaArith.Compare
import TCSlib.Complexity.CircuitComplexity.FormulaArith.ModSum

/-!
# Formula arithmetic

Shared combinators and arithmetic on `BoolCircuit.TreeCircuit` formulas: the circuit and formula
gadget layer of `machine-library-design.md` ("Circuit and formula gadgets").  New formulas are
assembled from it rather than built by hand.

## Contents

- `FormulaArith.Combinators`: the balanced binary gate `BoolCircuit.TreeCircuit.balanced` (fan-in
  two, `⌈log₂ |cs|⌉ + 1` extra depth), with its value, fan-in, depth and size lemmas; De Morgan
  negation `neg`, substitution `subst`, `rename`, `const`, and the gadgets `and2`, `or2`, `xor2`,
  `xor3`, `maj3`.
- `FormulaArith.CarrySave`: formula numbers (`val`) and the carry-save (3:2) reduction to two.
- `FormulaArith.Compare`: the carry-out `carryOut` and the comparison with a constant `geConst`.
- `FormulaArith.ModSum`: the modular interval sum `modSumInterval` and its depth `modSumDepth`.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false
