/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Pseudorandom.Indistinguishability
import TCSlib.Cryptography.Pseudorandom.Generators
import TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs
import TCSlib.Cryptography.Pseudorandom.GeneratorFromPermutation
import TCSlib.Cryptography.Pseudorandom.Functions
import TCSlib.Cryptography.Pseudorandom.NextBit.Concrete
import TCSlib.Cryptography.Pseudorandom.NextBit

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Pseudorandomness

The finite reductions of [Gar26, Chapter 3] give explicit adversaries and advantage bounds
at a fixed parameter. The asymptotic results of [PS10, §§3.1–3.8] add polynomial-time
evaluators and reductions, and quantify security by negligible advantage.

## Main definitions

`TCSlib.Cryptography.prgAdv` compares a generator's output with a uniform draw
from its output type.
`TCSlib.Cryptography.prfAdv` compares a keyed oracle with a random function.
`TCSlib.Cryptography.PRG` describes a length-regular generator.

## Main results

`TCSlib.Cryptography.exists_prgExtRed_ge` transfers a distinguisher for an iterated
generator to the one-bit generator. The new advantage is at least the original advantage
divided by the number of steps. `TCSlib.Cryptography.ggm_prfAdv_le` bounds the
advantage against the GGM keyed family by a sum of advantages against its generator.

## Contents

* `Indistinguishability` gives randomized post-processing and multicopy hybrids
  [Gar26, Lemmas 3.2 and 3.3].
* `Generators` gives the generator advantage, iteration, and the stretch reduction
  [Gar26, Definition 3.5 and Theorem 3.1].
* `Generators.Asymptotic.Defs` gives the length-regular PRG interface and security
  contract [PS10, Definition 77.1].
* `GeneratorFromPermutation` gives the reduction from distinguishing the generator
  to predicting a hard-concentrate bit [Gar26, Theorem 3.2].
* `Functions` leads to the oracle adversary model, lazy sampling, and the finite GGM
  proof in `TCSlib.Cryptography.Pseudorandom.Functions.GGM` [Gar26, Theorem 3.3].
* `NextBit.Concrete` gives the finite next-bit experiment and both quantitative reductions.
* `NextBit` implements the reductions as machines and characterizes pseudorandom ensembles.

## Asymptotic routes

* **Ensembles and next-bit prediction.** `TCSlib.Cryptography.Asymptotic.Ensembles`
  defines `TCSlib.Cryptography.Ensemble.Pseudorandom` in the shared ensemble model.
  `TCSlib.Cryptography.Ensemble.pseudorandom_iff_prgAdv` in
  `TCSlib.Cryptography.Pseudorandom.Generators.Asymptotic.Defs` characterizes it by
  negligible concrete PRG advantage. `TCSlib.Cryptography.PRG.Secure` packages efficiency
  and pseudorandomness for a generator.
  In `TCSlib.Cryptography.Pseudorandom.NextBit`,
  `TCSlib.Cryptography.Ensemble.NextBitUnpredictable.pseudorandom` proves
  the next-bit test complete [PS10, Theorem 75.4] and
  `TCSlib.Cryptography.Ensemble.Pseudorandom.nextBitUnpredictable` gives the converse.
* **One-way permutation to PRG.** In `TCSlib.Cryptography.Asymptotic.HardCore`,
  `TCSlib.Cryptography.owp_hardcore_prg` packages a secure one-bit-stretch generator
  from a one-way permutation family and its hard-core predicate [PS10, Theorem 79.4].
* **Stretch extension.** In the same module, `TCSlib.Cryptography.prg_expand` lifts
  the finite hybrid argument to show that expanding a secure one-bit generator to any
  polynomial output length greater than the seed length preserves security
  [PS10, Lemma 80.5].
  In `TCSlib.Cryptography.Asymptotic.HardCoreLemmas`,
  `TCSlib.Cryptography.exists_expandEvaluator` provides the efficient evaluator
  for the extended generator and `TCSlib.Cryptography.expandRedMachine_distinguisher`
  identifies the efficient reduction's behavior with the finite distinguisher.
* **PRG to PRF.** `TCSlib.Cryptography.Asymptotic.PRF` defines `TCSlib.Cryptography.PRF`
  and supplies length doubling via `TCSlib.Cryptography.PRG.Secure.doubling`.
  `TCSlib.Cryptography.exists_ggmPRF_evaluator` implements GGM in polynomial time,
  `TCSlib.Cryptography.exists_ggmBitsDist_nuppt` implements the finite hybrid
  reduction as a non-uniform polynomial-time adversary, and `TCSlib.Cryptography.ggmPRF_prf`
  proves security. `TCSlib.Cryptography.exists_prf_of_exists_prg` composes the steps
  [PS10, Theorem 97.3].
* **Encryption.** The secure PRG feeds the single-message scheme in
  `TCSlib.Cryptography.Asymptotic.Encryption` via `TCSlib.Cryptography.prgScheme_singleMessageSecure`.
  The PRF feeds the fixed-vector multi-message scheme in
  `TCSlib.Cryptography.Asymptotic.MultiMessage` via `TCSlib.Cryptography.prfScheme_multiMessageSecure`
  [PS10, Theorems 92.2 and 99.2]. Both scheme proofs take a matching polynomial-time evaluator.
  `TCSlib.Cryptography.exists_multiMessageSecure_of_exists_prg` composes GGM with the
  PRF-based scheme, using the evaluator supplied by the PRF efficiency proof.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Chapter 3.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed.,
  January 2010, §§3.1–3.9.
-/
