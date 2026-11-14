/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Randomness.Extraction
import TCSlib.Cryptography.Randomness.Extraction.Rejection
import TCSlib.Cryptography.Randomness.Extraction.Sampler
import TCSlib.Cryptography.Randomness.Learning
import TCSlib.Cryptography.Randomness.BPPBridge
import TCSlib.Cryptography.Randomness.Derandomization

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Randomness, learning and derandomization

The definitions, constructions and theorem statements of [PS10, Chapter 8].
The individual modules record deviations, proof sketches and outstanding admissions.

## Main definitions

See the definitions and construction modules listed below.

## Main results

See the theorem statements and correctness results in the constituent modules.

## Contents

* `Extraction` — no efficient one-bit extractor for the stated efficient-source class.
* `Learning` — PRFs give a hard-to-predict concept class.
* `BPPBridge` — the public bridge from BPP computations to distinguishers.
* `Derandomization` — PRGs give the BPP deterministic-time inclusion.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010.
-/
