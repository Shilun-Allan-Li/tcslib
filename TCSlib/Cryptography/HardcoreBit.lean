/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.HardcoreBit.Basic
import TCSlib.Cryptography.HardcoreBit.PairwiseIndependence
import TCSlib.Cryptography.HardcoreBit.NoFixedBit
import TCSlib.Cryptography.HardcoreBit.InnerProduct
import TCSlib.Cryptography.HardcoreBit.ThreeQuarters
import TCSlib.Cryptography.HardcoreBit.GoldreichLevin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-concentrate bits and the Goldreich–Levin theorem

The concrete layer of [Gar26, §2.5]: one fixed security parameter, adversaries as
functions of their input and uniform coins, and every reduction an explicit inverter
built from the predictor with an exact inequality between success probabilities.

## Contents

* `TCSlib.Cryptography.HardcoreBit.Basic`: algebra of uniform averages, maps pushing
  uniform to uniform, the good-set argument.
* `TCSlib.Cryptography.HardcoreBit.PairwiseIndependence`: Definition 2.4, Chebyshev's
  inequality (Theorem 2.4), majority votes, pairwise uniformity of subset XORs.
* `TCSlib.Cryptography.HardcoreBit.NoFixedBit`: Claim 2.3, no fixed input bit is
  hard-concentrate.
* `TCSlib.Cryptography.HardcoreBit.InnerProduct`: the setting `g(x, r) = f(x) ‖ r`,
  `B(x, r) = ⟨x, r⟩`, and the super simple case of Theorem 2.3.
* `TCSlib.Cryptography.HardcoreBit.ThreeQuarters`: the simple case of Theorem 2.3
  (prediction `≥ 3/4 + ε`).
* `TCSlib.Cryptography.HardcoreBit.GoldreichLevin`: the real case of Theorem 2.3
  (prediction `≥ 1/2 + ε`).

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5.
-/
