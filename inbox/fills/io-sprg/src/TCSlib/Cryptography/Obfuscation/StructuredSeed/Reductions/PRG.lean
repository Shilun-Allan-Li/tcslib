/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG.Defs
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG.Encoding
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG.Hop

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The explicit advice-taking JLS Boolean PRG reduction

## Main definitions

The definitions are imported from the children listed below.

## Main results

The reduction hop and encoding bounds are re-exported from the children.

## Contents

* `Defs`: canonical challenge, finite advice, encoders, preprocessing and readers.
* `Encoding`: the original three injection and polynomial advice-bound theorems.
* `Hop`: actual-law sampler/verdict/averaging glue and the final PRG hop.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026,
  Lemma 4.2, p. 19; Definition 3.4, p. 11.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8.

Dv4, Dv8, Dv9, Dv12, Dv14, Dv15 and Dv16 remain documented in the owning children.
Every old public full name, header, definition and statement docstring is retained.
-/
