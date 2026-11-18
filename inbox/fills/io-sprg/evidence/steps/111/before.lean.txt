/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Obfuscation.StructuredSeed.Buckets
import TCSlib.Cryptography.Games.Bridges.Experiments
import TCSlib.Cryptography.Authentication.Signatures.Lamport.Averaging
import TCSlib.Cryptography.OneWayFunctions.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.Complex.Exponential

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Finite bucket-load bounds for the JLS error analysis

## Main definitions

None. Bucket fibers are read through the existing `Buckets` interface.

## Main results

* `Internal.binomial_bound` gives the explicit exponential binomial estimate.
* `Internal.bucket_tail` bounds a fixed bucket's intersection with any fixed bad set.
* `Internal.some_bucket_tail` applies the existing finite union bound over buckets.
* `Internal.full_bucket_tail` and `Internal.some_full_bucket_tail` cover full loads.

## References

* [JLS26] A. Jain, H. Lin, A. Sahai, *Indistinguishability Obfuscation from
  Well-Founded Assumptions*, J. ACM 73(1), Article 1, February 2026,
  proof of Claim 4.2, p. 20.

Disclosed integral refinement: a load strictly above t contains t+1 distinct elements,
so the exact finite bounds use t+1 rather than the paper's weaker t-element bound.
The bounds include t=0 and oversized thresholds. Dv7's eventual construction-level
estimates are derived later; these finite combinatorial bounds hold at every size.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes,
  3rd ed., January 2010, Definition 26.8 (non-uniform PPT adversaries).
-/

namespace TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal

/-- For positive k, `choose(n,k) ≤ (exp(1)*n/k)^k`.
[JLS26, proof of Claim 4.2, p. 20]. The estimate holds even when k>n; unlike the paper's
presentation, it need not assume a nonzero binomial coefficient.

**Proof sketch.** Reuse Nat.choose_le_pow_div. Apply the exponential-series term bound
Real.pow_div_factorial_le_exp at x=k to bound the reciprocal factorial by (exp(1)/k)^k,
then multiply by n^k and combine the powers. No separate Stirling result is rederived. -/
theorem binomial_bound (n k : ℕ) (hk : 0 < k) :
    (Nat.choose n k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / k) ^ k := sorry

/-- For uniform bucket placement, a fixed bucket contains more than t elements of a fixed
set S with probability at most `choose(|S|,t+1)/B^(t+1)`.
[JLS26, proof of Claim 4.2, p. 20]. Disclosed refinement: the strict load threshold
uses t+1 distinct witnesses, including t=0 and thresholds at least |S|.

**Proof sketch.** Any overflowing intersection contains a (t+1)-element subset of S.
Apply the existing uprob_exists_le to these subsets. For each fixed subset, split its
coordinates from the unused coordinates with an explicit product equivalence and use
OneWay.uprob_pi_forall; every selected coordinate equals the bucket label with probability
1/B. Count the subsets with the existing powerset-cardinality theorem. -/
theorem bucket_tail {m B : ℕ} [NeZero B] (S : Finset (Fin m)) (b : Fin B) (t : ℕ) :
    uprob (fun φ : Fin m → Fin B => t < (Buckets.bucket φ b ∩ S).card) ≤
      (Nat.choose S.card (t + 1) : ℝ) / (B : ℝ) ^ (t + 1) := sorry

/-- For uniform placement, some bucket contains more than t elements of S with probability
at most `B*choose(|S|,t+1)/B^(t+1)`.
[JLS26, proof of Claim 4.2, p. 20]. Disclosed refinement: the finite strict-threshold
estimate uses t+1, and counts all B buckets explicitly.

**Proof sketch.** Apply the published uprob_exists_le over all finite bucket labels,
substitute bucket_tail for each label, and read the cardinality of Fin B. -/
theorem some_bucket_tail {m B : ℕ} [NeZero B] (S : Finset (Fin m)) (t : ℕ) :
    uprob (fun φ : Fin m → Fin B => ∃ b : Fin B, t < (Buckets.bucket φ b ∩ S).card) ≤
      (B : ℝ) * ((Nat.choose S.card (t + 1) : ℝ) / (B : ℝ) ^ (t + 1)) := sorry

/-- A fixed bucket's full load exceeds t with probability at most
`choose(m,t+1)/B^(t+1)`. [JLS26, proof of Claim 4.2, p. 20]. Disclosed refinement:
this uses the t+1-element witness for a strictly overflowing load.

**Proof sketch.** Specialize bucket_tail to the full set, read Buckets.load through
load_eq, and use the existing intersection and finite-universe cardinality lemmas. -/
theorem full_bucket_tail {m B : ℕ} [NeZero B] (b : Fin B) (t : ℕ) :
    uprob (fun φ : Fin m → Fin B => t < Buckets.load φ b) ≤
      (Nat.choose m (t + 1) : ℝ) / (B : ℝ) ^ (t + 1) := sorry

/-- Some bucket's full load exceeds t with probability at most
`B*choose(m,t+1)/B^(t+1)`. [JLS26, proof of Claim 4.2, p. 20]. Disclosed refinement:
the finite bound keeps the exact strict-threshold witness and explicit bucket factor.

**Proof sketch.** Specialize some_bucket_tail to the full set and read the load,
intersection and universe-cardinality equations through their published readers. -/
theorem some_full_bucket_tail {m B : ℕ} [NeZero B] (t : ℕ) :
    uprob (fun φ : Fin m → Fin B => ∃ b : Fin B, t < Buckets.load φ b) ≤
      (B : ℝ) * ((Nat.choose m (t + 1) : ℝ) / (B : ℝ) ^ (t + 1)) := sorry

end TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal
