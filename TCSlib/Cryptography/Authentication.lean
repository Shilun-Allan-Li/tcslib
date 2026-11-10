/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Authentication.PRFMAC
import TCSlib.Cryptography.Authentication.MAC.FromPRF
import TCSlib.Cryptography.Authentication.Lamport
import TCSlib.Cryptography.Authentication.DLHash
import TCSlib.Cryptography.Authentication.HashAndSign

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Authentication: MACs, signatures and hashing

The definitions, constructions and theorem statements of [PS10, Chapter 5].
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Encoding` — shared encodings for the games and algorithms.
* `MAC.Defs` — the MAC interface and unforgeability game.
* `Defs` — signature schemes, collision-resistant hashing and their games.
* `MAC.FromPRF` — the PRF MAC construction, correctness proof and security statement.
* `PRFMAC` — compatibility import for the PRF MAC.
* `Lamport` — Lamport one-time signatures and their security statement.
* `DLHash` — the discrete-log collision-resistant hash construction.
* `HashAndSign` — hash-and-sign and the one-time security statement.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
-/
