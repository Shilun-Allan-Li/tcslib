/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.PRF
import TCSlib.Cryptography.Asymptotic.Encryption
import TCSlib.Cryptography.Asymptotic.MultiMessageLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import Mathlib.Data.Nat.Choose.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# PRF-based private-key encryption compatibility import

## Main definitions

`Encryption.PrivateKey.FromPRF` defines the scheme of [PS10, Algorithm 99.1].

## Main results

The import exposes the finite hybrid, next-query reduction, and fixed-vector security
proof [PS10, Theorem 99.2].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.7, Definition 93.1, and §3.9, Algorithm 99.1 and Theorem 99.2.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.4 (oracle adversaries and PRF advantage).
-/
