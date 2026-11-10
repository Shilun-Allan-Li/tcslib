/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import TCSlib.Cryptography.Asymptotic.SamplingFinDist
import TCSlib.Cryptography.Asymptotic.Permutations
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Asymptotic.ReductionSupport
import TCSlib.Cryptography.Asymptotic.Ensembles
import TCSlib.Cryptography.Asymptotic.OneWay
import TCSlib.Cryptography.Asymptotic.Collections
import TCSlib.Cryptography.Asymptotic.Universal
import TCSlib.Cryptography.Pseudorandom.NextBit
import TCSlib.Cryptography.Asymptotic.GoldreichLevinDomain
import TCSlib.Cryptography.Asymptotic.HardCoreCollection
import TCSlib.Cryptography.Asymptotic.HardCore.Functions
import TCSlib.Cryptography.Asymptotic.HardCore
import TCSlib.Cryptography.Asymptotic.HardCorePermutation.GoldreichLevin
import TCSlib.Cryptography.Asymptotic.HardCoreClaims
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.HybridLemmas
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF.ReductionMachine
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRF
import TCSlib.Cryptography.Asymptotic.BlockEncryptor
import TCSlib.Cryptography.Encryption.PublicKey.Hybrid
import TCSlib.Cryptography.Encryption.PublicKey.TrapdoorPredictor
import TCSlib.Cryptography.Encryption.PublicKey.Trapdoor

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Cryptography — the asymptotic layer

The asymptotic layer of the Pass–shelat campaign ([PS10, Chapters 2–3]; plan
`PassShelatChapter2-4Plan.md`, foundation decisions D2–D7, D9, D10): the textbook definitions
of one-way functions, pseudorandomness, hard-core bits, encryption and pseudorandom functions
against non-uniform probabilistic polynomial-time adversaries (`Complexity.NUPPT`), and the
textbook theorems derived from the concrete reductions of
`TCSlib/Cryptography/{Foundations,OneWayFunctions,HardcoreBit,Pseudorandom}` [Gar26] plus the
machine-closure facts of `TCSlib/Complexity/Randomized`.

## Contents

* `Sampling` — statistical closeness `StatClose` and rejection sampling `rejectionSample`
  (the one sampling device, D10; the concrete lemmas C4, C5, C10 of the chapter 2 inventory);
  `Permutations` — rejection-sampled permutations `permFromCoins` with the campaign
  parameters `permBits`, `permTrials` and the failure bound `n · 2^{-n}`.
* `SamplingFinDist` — `StatClose` of samplers is `EpsClose` of their laws
  (`statClose_iff_epsClose_map`).
* `Adversary` — an `NUPPT` as an inverter, distinguisher or predictor of the concrete
  experiments (`decodeFin`, `padFin`, `invProbOpt`; [PS10, Definitions 24.6, 26.1, 27.3, 69.4,
  75.2, 78.3]).
* `ReductionSupport` gives shared adversary wrappers and their coin and run equations.
* `Ensembles` — ensembles and computational indistinguishability [PS10, Definitions 69.3,
  69.4], closure under efficient operations [PS10, Lemma 71.5], the hybrid lemma
  [PS10, Lemma 71.6], the prediction lemma [PS10, Lemma 73.8], the pairwise-independent
  sampling inequality [PS10, Appendix A].
* `OneWay` — function families, worst-case, strong and weak one-way functions
  [PS10, Definitions 26.1, 27.3, 28.4], Yao's hardness amplification [PS10, Theorems 35.1,
  35.2], one-way permutations.
* `Collections` — collections of one-way functions, one-way and trapdoor permutations
  [PS10, Definitions 41.1, 55.1, 56.1; Theorem 42.2].
* `Universal` — Levin's universal one-way function [PS10, Theorem 63.1, Algorithm 64.2].
* `Pseudorandom.Generators.Asymptotic.Defs` gives the PRG interface and relates it to
  pseudorandom ensembles [PS10, Definitions 74.1 and 77.1].
* `Pseudorandom.NextBit` gives the next-bit test and its completeness
  [PS10, Definition 75.2, Theorem 75.4, Algorithm 76.5].
* `GoldreichLevinDomain` gives the concrete Goldreich–Levin bound for `x` uniform on an
  encoded finite domain (the collection form of [PS10, Theorem 87.3]; run-3 audit P4-2).
* `HardCore` collects the Goldreich–Levin results for function families, collections,
  and balanced permutations [PS10, Definition 78.3 and Theorem 87.3].
* `HardCoreClaims` supplies the concrete claims used in the Goldreich–Levin proof.
* `Pseudorandom.Generators.Asymptotic.FromPermutation` builds a secure PRG from a
  one-way permutation [PS10, §3.4].
* `Encryption.PrivateKey.FromPRG` gives the pad scheme and single-message security
  [PS10, Definitions 24.7, 91.1, 93.1; Algorithm 92.1; Theorem 92.2].
* `Pseudorandom.Functions.Asymptotic.Defs` gives the oracle and PRF contracts.
  `Pseudorandom.Functions.Asymptotic.GGM` gives the PRF construction and its security
  [PS10, Definitions 96.1, 96.2 and Theorem 97.3].
* `Encryption.PrivateKey.FromPRF` gives multi-message secure private-key encryption
  from a PRF [PS10, Definition 93.1; Algorithm 99.1; Theorem 99.2].
* `BlockEncryptor` gives the block-wise encryptor machine and its efficiency
  [PS10, p. 103, Theorem 103.d of the inventory].
* `Encryption.PublicKey.Trapdoor` gives the public-key scheme from a trapdoor permutation
  and its security [PS10, Definitions 102.1, 102.2; Algorithm 104.3; Theorem 104.4].

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026.
-/
