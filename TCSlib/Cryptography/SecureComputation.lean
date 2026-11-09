/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs
import TCSlib.Cryptography.SecureComputation.ObliviousTransfer
import TCSlib.Cryptography.SecureComputation.SpecialEncryption
import TCSlib.Cryptography.SecureComputation.SpecialEncryptionSecurity
import TCSlib.Cryptography.SecureComputation.Garbling
import TCSlib.Cryptography.SecureComputation.GarblingSpecial
import TCSlib.Cryptography.SecureComputation.GarblingSecurity
import TCSlib.Cryptography.SecureComputation.Hybrid
import TCSlib.Cryptography.SecureComputation.Compose
import TCSlib.Cryptography.SecureComputation.ComposePhases
import TCSlib.Cryptography.SecureComputation.ComposeSecurity
import TCSlib.Cryptography.SecureComputation.Yao
import TCSlib.Cryptography.SecureComputation.YaoReal

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Secure two-party computation

The definitions, constructions and theorem statements of [PS10, §6.2] and [Gol04, §7.3].
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Defs` — honest-but-curious security with efficient parties and bounded messages.
* `ObliviousTransfer` — five-message oblivious transfer from trapdoor permutations.
* `SpecialEncryption` — the nested special-encryption construction and correctness.
* `SpecialEncryptionSecurity` — special-encryption security statements.
* `Garbling` — deterministic garbling and correctness.
* `GarblingSpecial` — garbling with the special-encryption construction.
* `GarblingSecurity` — the probabilistic garbling-security statement.
* `Hybrid` — the OT-hybrid computation model.
* `Compose` — sequential composition of a hybrid protocol with an implementation.
* `ComposePhases` — the phase identities for sequential composition.
* `ComposeSecurity` — the composition security statement.
* `Yao` — Yao’s protocol in the OT-hybrid model.
* `YaoReal` — the real protocol and its security statement by composition.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press, 2004.
-/
