/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Samplers
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Claim42.Load

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The uniformly small JLS error event

## Main definitions

* The three failure events, the exact joint law, and `Params.errProb`.

## Contents

* `Claim42.Load`: finite binomial and bucket-tail bounds.

## Main results

* `Params.claim42`: eventual error at most 2^(-κ), uniformly in the public prime.
* Locality/Markov and event-decomposition statements support the error analysis.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026, §§2-4.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed

open TCSlib.Cryptography.Games
open scoped BigOperators

namespace Params

/-- The first failure condition is too many bad outputs in repetition k
[JLS26, proof of Claim 4.2, pp. 19-20]. Dv3 uses the rounded threshold Γ. -/
noncomputable def Cond1 (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (d : P.Draw κ pp) (k : Fin κ) : Prop :=
  P.Γ κ < (P.badSet κ pp I (fun i => P.noiseValue κ pp ((d.2 k).2 i))).card

/-- The first condition compares the bad-output count with Γ; glue. -/
theorem cond1_iff (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (d : P.Draw κ pp) (k : Fin κ) :
    P.Cond1 κ pp I d k ↔
      P.Γ κ < (P.badSet κ pp I (fun i => P.noiseValue κ pp ((d.2 k).2 i))).card :=
  Iff.rfl

/-- The second failure condition is more than t bad outputs in some bucket
[JLS26, proof of Claim 4.2, pp. 19-20]. Dv3 uses an integer threshold. -/
noncomputable def Cond2 (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (d : P.Draw κ pp) (k : Fin κ) : Prop :=
  ∃ b : Fin (P.B κ), P.t κ <
    (Buckets.bucket I.2.1 b ∩
      P.badSet κ pp I (fun i => P.noiseValue κ pp ((d.2 k).2 i))).card

/-- The second condition is the finite bucket-overload event for bad outputs; glue. -/
theorem cond2_iff (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) (d : P.Draw κ pp) (k : Fin κ) :
    P.Cond2 κ pp I d k ↔ ∃ b : Fin (P.B κ), P.t κ <
      (Buckets.bucket I.2.1 b ∩
        P.badSet κ pp I (fun i => P.noiseValue κ pp ((d.2 k).2 i))).card := Iff.rfl

/-- The third failure condition is a bucket beyond capacity
[JLS26, proof of Claim 4.2, pp. 19-20]. This event is shared by all repetitions. -/
noncomputable def Cond3 (P : Params) (κ : ℕ) (pp : PrimeParam κ)
    (I : P.Idx' κ pp) : Prop := Buckets.overfull I.2.1 (P.cap κ)

/-- The third condition is the overfull-placement predicate; glue. -/
theorem cond3_iff (P : Params) (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp) :
    P.Cond3 κ pp I ↔ Buckets.overfull I.2.1 (P.cap κ) := Iff.rfl

/-- The proof-facing joint law retains index and full seed-core output
[JLS26, Claim 4.2, p. 19]. Dv17 uses exact finite draws, without a coin sampler. -/
noncomputable def jointLaw (P : Params) (κ : ℕ) (pp : PrimeParam κ) :
    ProbComp (P.Idx' κ pp × P.SdCoreOut κ pp) :=
  (P.idSamp' κ pp).bind fun I => (fun x => (I, x)) <$> P.sdSampFull κ pp I

/-- The joint law samples index and the corresponding core output; glue. -/
theorem jointLaw_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) :
    P.jointLaw κ pp = (P.idSamp' κ pp).bind fun I =>
      (fun x => (I, x)) <$> P.sdSampFull κ pp I := rfl

/-- Error probability is the exact chance that SdSamp' finds no successful repetition
[JLS26, Claim 4.2, p. 19]. Dv7 leaves its value explicit at every κ and pp. -/
noncomputable def errProb (P : Params) (κ : ℕ) (pp : PrimeParam κ) : ℝ :=
  ProbComp.prob ((P.idSamp' κ pp).bind fun I => P.sdSampFull κ pp I)
    (fun x => x.err = true)

/-- Error probability is the stated exact-law event; glue. -/
theorem errProb_eq (P : Params) (κ : ℕ) (pp : PrimeParam κ) :
    P.errProb κ pp = ProbComp.prob
      ((P.idSamp' κ pp).bind fun I => P.sdSampFull κ pp I) (fun x => x.err = true) := rfl

/-- Error probabilities are nonnegative; glue.

**Proof sketch.** Use the existing nonnegativity of ProbComp.prob. -/
theorem errProb_nonneg (P : Params) (κ : ℕ) (pp : PrimeParam κ) :
    0 ≤ P.errProb κ pp := sorry

/-- Locality bounds the expected number of bad output coordinates by cLoc*m/W
[JLS26, proof of Claim 4.2, p. 20]. Dv3 uses exact rounded noise, and the bound
is uniform in every public prime and index.

**Proof sketch.** Union-bound the error events in each output's at most cLoc variables,
then sum their indicator expectations using the existing probability readers. -/
theorem badSet_expect_le (P : Params) {cLoc : ℕ} (hLoc : P.R.HasLocality cLoc)
    (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp) :
    ProbComp.expect (ProbComp.sample (Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p))
      (fun r => ((P.badSet κ pp I (fun i => P.noiseValue κ pp (r i))).card : ℝ)) ≤
        (cLoc : ℝ) * P.m κ / P.W κ := sorry

/-- Markov's inequality bounds the too-many-bad event using Γ+1
[JLS26, proof of Claim 4.2, p. 20]. Dv3 makes the strict integer threshold
explicit, avoiding any division by Γ=0.

**Proof sketch.** On the event, the integer bad count is at least Γ+1. Apply the published
Markov inequality and the locality expectation estimate, using W>0. -/
theorem cond1_prob_le (P : Params) {cLoc : ℕ} (hLoc : P.R.HasLocality cLoc)
    (κ : ℕ) (pp : PrimeParam κ) (I : P.Idx' κ pp) :
    ProbComp.prob (ProbComp.sample (Fin (P.n κ) → Fin (P.W κ) × ZMod pp.p))
      (fun r => P.Γ κ < (P.badSet κ pp I (fun i => P.noiseValue κ pp (r i))).card) ≤
        (cLoc : ℝ) * P.m κ / ((P.W κ : ℝ) * (P.Γ κ + 1)) := sorry

/-- The error event is bounded by common capacity failure, the sparse-but-overloaded
repetitions, and simultaneous bad-count failure [JLS26, proof of Claim 4.2, p. 21].
Dv7 keeps every probability explicit before taking eventual estimates.

**Proof sketch.** Read firstGood's failure condition. If no repetition succeeds, either the
common capacity event holds, some repetition has Cond2 without Cond1, or all have Cond1.
Apply the existing finite-event union bound through the uniform-draw bridge. -/
theorem errProb_le_decomposition (P : Params) (κ : ℕ) (pp : PrimeParam κ) :
    P.errProb κ pp ≤
      ProbComp.prob (P.jointLaw κ pp) (fun x => P.Cond3 κ pp x.1) +
      (∑ k : Fin κ, ProbComp.prob (P.jointLaw κ pp)
        (fun x => P.Cond2 κ pp x.1 x.2.draw k ∧ ¬ P.Cond1 κ pp x.1 x.2.draw k)) +
      ProbComp.prob (P.jointLaw κ pp) (fun x => ∀ k, P.Cond1 κ pp x.1 x.2.draw k) := sorry

/-- For all sufficiently large κ the error event has probability at most 2^(-κ),
uniformly in every public prime [JLS26, Claim 4.2, pp. 19-21]. Dv3 uses the rounded
rational noise schedule (SP-W1); Dv7 makes the common eventual threshold explicit.

**Proof sketch.** Use the three-event decomposition. Locality and Markov bound Cond1,
conditionally on each fixed generator index. Independent noise repetitions then bound
simultaneous Cond1. Bucket-tail bounds control Cond2 outside Cond1 and the common Cond3.
The bucket count is polynomial; logarithmic growth and the resulting exponential bounds
make their sum at most 2^(-κ), with no dependence on pp. -/
theorem claim42 (P : Params) {cLoc : ℕ} (hLoc : P.R.HasLocality cLoc) :
    ∃ κ₀, ∀ κ ≥ κ₀, ∀ pp : PrimeParam κ,
      P.errProb κ pp ≤ (2 : ℝ)⁻¹ ^ κ := sorry

end Params
end TCSlib.Cryptography.Obfuscation.StructuredSeed
