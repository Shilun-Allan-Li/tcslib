/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pairing.Group
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Symmetric bilinear groups and the bilinear Diffie–Hellman assumptions

## Contents

* `Group`: abstract symmetric bilinear groups of prime order, their generators, bilinearity and
  non-degeneracy facts.
* `Assumptions`: the BDH and Decision BDH experiments and assumptions; Decision BDH implies BDH.
* `Operations`: the efficiency contract of a generator (group operations and pairing as
  polynomial-time string functions).

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004,
  §2.2 and §3.1.
* [Jou00] A. Joux, *A One Round Protocol for Tripartite Diffie–Hellman*, ANTS-IV, LNCS 1838,
  pp. 385–393, Springer, 2000.
-/
