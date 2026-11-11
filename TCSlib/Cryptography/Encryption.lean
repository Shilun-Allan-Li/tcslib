/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey
import TCSlib.Cryptography.Encryption.Symmetric
import TCSlib.Cryptography.Encryption.PublicKey
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveSecurity

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cryptographic encryption constructions

## Contents

* `PrivateKey` gives the Pass–shelat scheme interfaces, security games and PRG-, PRF- and
  tag-based constructions.
* `Symmetric` gives the direct Regev private-key construction and its concrete experiments.
* `PublicKey` gives the scheme interfaces and security games, the trapdoor route shared by
  RSA and Rabin, and the ElGamal and Regev constructions.

The private-key routes have different interfaces. The construction maps identify the
game, hypotheses and proof status of each result.
-/
