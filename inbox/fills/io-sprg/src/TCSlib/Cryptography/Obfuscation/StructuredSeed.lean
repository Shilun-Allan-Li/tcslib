/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.LPN
import TCSlib.Cryptography.Obfuscation.StructuredSeed.BoolPRG
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Degree
import TCSlib.Cryptography.Obfuscation.StructuredSeed.PolyTerms
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Defs
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Params
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Encoding
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets
import TCSlib.Cryptography.Obfuscation.StructuredSeed.SparseFactor
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Polys
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Samplers
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Correctness
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Stretch
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Load
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Hybrids
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.LPN
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Reductions.PRG
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Security
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Targets

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Structured-seed pseudorandom generators

## Contents

* `LPN`: the lpn component.
* `BoolPRG`: the boolprg component.
* `Degree`: the degree component.
* `PolyTerms`: the polyterms component.
* `Defs`: the defs component.
* `Params`: the params component.
* `Encoding`: explicit finite coordinates and construction encodings.
* `Buckets`: the buckets component.
* `SparseFactor`: the sparsefactor component.
* `Polys`: the polys component.
* `Samplers`: the samplers component.
* `Correctness`: the correctness component.
* `Stretch`: the stretch component.
* `Claim42.Load`: the claim42 load component.
* `Claim42`: the claim42 component.
* `Hybrids`: the hybrids component.
* `Reductions.LPN`: the reductions lpn component.
* `Reductions.PRG`: the reductions prg component.
* `Security`: the security component.
* `Targets`: the targets component.

## Main definitions

The imported modules provide the raw algorithm bundles, efficient primitives and Phase B targets.

## Main results

The imported modules state correctness, stretch and security for the structured-seed construction.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/
