/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Basic
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

* `Basic`: reusable fixed-width tagged-list encoding lemmas.
* `LPN`: exact scalar noise, the canonical `LPNFamily.Raw` view and efficient `LPNFamily`.
* `BoolPRG`: indexed Boolean generators, multilinear representations, locality and stretch.
* `Degree`: `pubDegree` and `privDegree` with weighted polynomial degree bounds.
* `PolyTerms`: finite polynomial term lists, `PolyTerms.denote` and faithful term encodings.
* `Defs`: public prime inputs, raw and efficient sPRG syntax, security and complexity.
* `Params`: rational noise data, power schedules, rounded dimensions and `lpnFamily_raw`.
* `Encoding`: explicit finite coordinates and construction encodings.
* `Buckets`: deterministic bucket ranks, optional grid positions and correction matrices.
* `SparseFactor`: row-major sparse factors and reconstruction for bounded support.
* `Polys`: the tensor and correction maps `G1`-`G4` and their public/private degree bounds.
* `Samplers`: exact joint seed cores, their derived laws, `eval'` and `jlsSPRG_raw`.
* `Correctness`: sampled-seed `G4_eval_eq`, `eval'_correct` and `jls_hasComplexity`.
* `Stretch`: the sufficient exponent `E0` and growing-seed `jls_hasPolyStretch`.
* `Claim42.Load`: binomial estimates and finite bucket-occupancy tail bounds.
* `Claim42`: `Params.claim42`, the error bound uniform in every public prime.
* `Hybrids`: exact hybrid/chain games, endpoint acceptance equalities and statistical hops.
* `Reductions.LPN`: canonical LPN advice/preprocessing and the every-realiser `lpn_hop`.
* `Reductions.PRG`: Boolean challenge advice/preprocessing and the every-realiser `prg_hop`.
* `Security`: `prop41`, raw negligible/subexponential security and own-family existence.
* `Targets`: six uniform efficiency targets, conditional links and primitive assemblies.

## Main definitions

The principal types are `BoolPRG`, `LPNFamily.Raw`, `LPNFamily`, `SPRG.Raw`, `SPRG`
and `Params`. `Params.Targets` names the uniform efficiency hypotheses used in assembly.

## Main results

`Params.G4_eval_eq` and `jls_hasComplexity` give algebraic correctness;
`jls_hasPolyStretch` gives growing-seed stretch. `prop41` bounds advantage, and
`theorem41` gives raw security, complexity and stretch from the stated assumptions.
`theorem41_of_targets` and the efficient existence results are conditional on the targets.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/
