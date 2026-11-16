/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.KeyExchange.Joux

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Key exchange

## Contents

* `Joux`: Joux's one-round tripartite Diffie–Hellman over a symmetric bilinear group, its
  correctness and its key indistinguishability under Decision BDH.

## References

* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000.
-/
