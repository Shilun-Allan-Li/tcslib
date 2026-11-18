/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Assembly
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Garbling
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.LinearEfficiency
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.MatrixDH
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Scheme
import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.Wee20.Targets.Sim

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PHFE uniform-efficiency targets and pure assembly

## Contents

* `Targets.Scheme`: the five honest-algorithm targets.
* `Targets.Sim`: the six targets for both concrete stateful simulators.
* `Targets.Garbling`: deterministic layered-garbling targets.
* `Targets.LinearEfficiency`: one machine with a linear-in-dimensions bound.
* `Targets.MatrixDH`: the L1 preprocessing target and its shared realisation link.
* `Targets.Assembly`: all targets and pure assembly of the four efficient interfaces.
-/
