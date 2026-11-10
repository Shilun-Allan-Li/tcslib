/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Authentication.Defs
import TCSlib.Cryptography.Authentication.Signatures.Defs
import TCSlib.Cryptography.Authentication.Encoding
import TCSlib.Cryptography.Authentication.MAC.Defs
import TCSlib.Cryptography.Authentication.PRFMAC
import TCSlib.Cryptography.Authentication.MAC.FromPRF
import TCSlib.Cryptography.Authentication.Lamport
import TCSlib.Cryptography.Authentication.Signatures.Lamport
import TCSlib.Cryptography.Authentication.DLHash
import TCSlib.Cryptography.Authentication.HashAndSign
import TCSlib.Cryptography.Authentication.Signatures.HashAndSign

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Authentication: MACs and signatures

The authentication constructions and games of [PS10, Chapter 5]. The hashing interface and
discrete-log construction are indexed in `TCSlib.Cryptography.Hashing`.
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Encoding` — shared encodings for the games and algorithms.
* `MAC.Defs` — the MAC interface and unforgeability game.
* `MAC.FromPRF` — the PRF-based MAC, correctness proof and security statement.
* `Signatures.Defs` — the signature interface and forgery games.
* `Signatures.Lamport` — the one-time signature construction from a strong one-way function.
* `Signatures.HashAndSign` — signatures for the hash family's full domain when the digest width fits.
* `Defs` — compatibility import for the authentication and hashing interfaces.
* `PRFMAC` — compatibility import for the PRF-based MAC.
* `Lamport` — compatibility import for Lamport signatures.
* `DLHash` — compatibility import for the discrete-log hash.
* `HashAndSign` — compatibility import for hash-and-sign.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
-/
