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
    (Nat.choose n k : ℝ) ≤ (Real.exp 1 * (n : ℝ) / k) ^ k := by
  have hkR : 0 < (k : ℝ) := Nat.cast_pos.mpr hk
  have hkpow : 0 < (k : ℝ) ^ k := pow_pos hkR k
  have hfact : 0 < (k.factorial : ℝ) := Nat.cast_pos.mpr (Nat.factorial_pos k)
  have hexp : Real.exp (k : ℝ) = Real.exp 1 ^ k := ?_
  swap
  · simpa only [mul_one] using Real.exp_nat_mul (1 : ℝ) k
  have hseries := Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg k) k
  rw [hexp] at hseries
  have hfac : 1 / (k.factorial : ℝ) ≤ (Real.exp 1 / (k : ℝ)) ^ k := ?_
  swap
  · rw [div_pow]
    apply (div_le_div_iff₀ hfact hkpow).2
    simpa only [one_mul] using (div_le_iff₀ hfact).1 hseries
  have hchoose : (Nat.choose n k : ℝ) ≤
      (n : ℝ) ^ k * (1 / (k.factorial : ℝ)) := ?_
  swap
  · simpa only [div_eq_mul_inv, one_mul] using (Nat.choose_le_pow_div (α := ℝ) k n)
  have hfinal := hchoose.trans
    (mul_le_mul_of_nonneg_left hfac (pow_nonneg (Nat.cast_nonneg n) k))
  have hbase : (n : ℝ) * (Real.exp 1 / (k : ℝ)) = Real.exp 1 * (n : ℝ) / k := ?_
  swap
  · ring
  rw [← mul_pow, hbase] at hfinal
  exact hfinal

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
      (Nat.choose S.card (t + 1) : ℝ) / (B : ℝ) ^ (t + 1) := by
  classical
  letI : Inhabited (Fin B) := ⟨b⟩
  have hfixed : ∀ T : Finset (Fin m),
      uprob (fun φ : Fin m → Fin B => ∀ j ∈ T, φ j = b) =
        1 / (B : ℝ) ^ T.card := ?_
  swap
  · intro T
    let e : (Fin m → Fin B) ≃
        (T → Fin B) × ({j : Fin m // j ∉ T} → Fin B) :=
      Equiv.piEquivPiSubtypeProd (fun j => j ∈ T) (fun _ => Fin B)
    have hsplit : uprob (fun φ : Fin m → Fin B => ∀ j ∈ T, φ j = b) =
        uprob (fun φ : Fin m → Fin B => ∀ j : T, (e φ).1 j = b) := ?_
    swap
    · apply OneWay.uprob_congr
      intro φ
      change (∀ j ∈ T, φ j = b) ↔ ∀ j : T, φ j = b
      simp only [Subtype.forall]
    have hrelabel :
        uprob (fun φ : Fin m → Fin B => ∀ j : T, (e φ).1 j = b) =
          uprob (fun fg : (T → Fin B) × ({j : Fin m // j ∉ T} → Fin B) =>
            ∀ j : T, fg.1 j = b) :=
      uprob_comp_equiv e
        (fun fg : (T → Fin B) × ({j : Fin m // j ∉ T} → Fin B) =>
          ∀ j : T, fg.1 j = b)
    have hfst :
        uprob (fun fg : (T → Fin B) × ({j : Fin m // j ∉ T} → Fin B) =>
          ∀ j : T, fg.1 j = b) =
            uprob (fun f : T → Fin B => ∀ j : T, f j = b) :=
      uprob_fst (β := {j : Fin m // j ∉ T} → Fin B)
        (fun f : T → Fin B => ∀ j : T, f j = b)
    have hpi : uprob (fun f : T → Fin B => ∀ j : T, f j = b) =
        uprob (fun a : Fin B => a = b) ^ Fintype.card T :=
      OneWay.uprob_pi_forall (ι := T) (fun a : Fin B => a = b)
    have hpoint : uprob (fun a : Fin B => a = b) = 1 / (B : ℝ) := ?_
    swap
    · simpa only [Fintype.card_fin] using OneWay.uprob_eq_one_div_card b
    calc
      uprob (fun φ : Fin m → Fin B => ∀ j ∈ T, φ j = b) =
          uprob (fun f : T → Fin B => ∀ j : T, f j = b) :=
        hsplit.trans (hrelabel.trans hfst)
      _ = uprob (fun a : Fin B => a = b) ^ Fintype.card T := hpi
      _ = (1 / (B : ℝ)) ^ Fintype.card T :=
        congrArg (fun x : ℝ => x ^ Fintype.card T) hpoint
      _ = 1 / (B : ℝ) ^ T.card := ?_
    rw [Fintype.card_coe, div_pow, one_pow]
  have hcover : ∀ φ : Fin m → Fin B,
      t < (Buckets.bucket φ b ∩ S).card →
        ∃ T ∈ S.powersetCard (t + 1), ∀ j ∈ T, φ j = b := ?_
  swap
  · intro φ hφ
    obtain ⟨T, hT, hcard⟩ := Finset.exists_subset_card_eq (Nat.succ_le_of_lt hφ)
    refine ⟨T, Finset.mem_powersetCard.mpr ⟨?_, hcard⟩, ?_⟩
    · intro j hj
      exact (Finset.mem_inter.mp (hT hj)).2
    · intro j hj
      have hjbucket := (Finset.mem_inter.mp (hT hj)).1
      simpa only [Buckets.bucket_eq, Finset.mem_filter, Finset.mem_univ,
        true_and] using hjbucket
  calc
    uprob (fun φ : Fin m → Fin B => t < (Buckets.bucket φ b ∩ S).card) ≤
        uprob (fun φ : Fin m → Fin B =>
          ∃ T ∈ S.powersetCard (t + 1), ∀ j ∈ T, φ j = b) :=
      uprob_mono (α := Fin m → Fin B) hcover
    _ ≤ Finset.sum (S.powersetCard (t + 1))
        (fun T => uprob (fun φ : Fin m → Fin B => ∀ j ∈ T, φ j = b)) :=
      uprob_exists_le (α := Fin m → Fin B) (S.powersetCard (t + 1))
        (fun (T : Finset (Fin m)) (φ : Fin m → Fin B) => ∀ j ∈ T, φ j = b)
    _ = Finset.sum (S.powersetCard (t + 1))
        (fun _ => 1 / (B : ℝ) ^ (t + 1)) := ?_
    _ = (Nat.choose S.card (t + 1) : ℝ) / (B : ℝ) ^ (t + 1) := ?_
  · apply Finset.sum_congr rfl
    intro T hT
    rw [hfixed T, (Finset.mem_powersetCard.mp hT).2]
  · rw [Finset.sum_const, Finset.card_powersetCard, nsmul_eq_mul]
    ring

/-- For uniform placement, some bucket contains more than t elements of S with probability
at most `B*choose(|S|,t+1)/B^(t+1)`.
[JLS26, proof of Claim 4.2, p. 20]. Disclosed refinement: the finite strict-threshold
estimate uses t+1, and counts all B buckets explicitly.

**Proof sketch.** Apply the published uprob_exists_le over all finite bucket labels,
substitute bucket_tail for each label, and read the cardinality of Fin B. -/
theorem some_bucket_tail {m B : ℕ} [NeZero B] (S : Finset (Fin m)) (t : ℕ) :
    uprob (fun φ : Fin m → Fin B => ∃ b : Fin B, t < (Buckets.bucket φ b ∩ S).card) ≤
      (B : ℝ) * ((Nat.choose S.card (t + 1) : ℝ) / (B : ℝ) ^ (t + 1)) := by
  classical
  have h :=
    (uprob_exists_le (Finset.univ : Finset (Fin B))
      (fun b (φ : Fin m → Fin B) => t < (Buckets.bucket φ b ∩ S).card)).trans
      (Finset.sum_le_sum (fun b _ => bucket_tail S b t))
  simpa only [Finset.mem_univ, true_and, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul] using h

/-- A fixed bucket's full load exceeds t with probability at most
`choose(m,t+1)/B^(t+1)`. [JLS26, proof of Claim 4.2, p. 20]. Disclosed refinement:
this uses the t+1-element witness for a strictly overflowing load.

**Proof sketch.** Specialize bucket_tail to the full set, read Buckets.load through
load_eq, and use the existing intersection and finite-universe cardinality lemmas. -/
theorem full_bucket_tail {m B : ℕ} [NeZero B] (b : Fin B) (t : ℕ) :
    uprob (fun φ : Fin m → Fin B => t < Buckets.load φ b) ≤
      (Nat.choose m (t + 1) : ℝ) / (B : ℝ) ^ (t + 1) := by
  simpa only [Buckets.load_eq, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    using (bucket_tail (Finset.univ : Finset (Fin m)) b t)

/-- Some bucket's full load exceeds t with probability at most
`B*choose(m,t+1)/B^(t+1)`. [JLS26, proof of Claim 4.2, p. 20]. Disclosed refinement:
the finite bound keeps the exact strict-threshold witness and explicit bucket factor.

**Proof sketch.** Specialize some_bucket_tail to the full set and read the load,
intersection and universe-cardinality equations through their published readers. -/
theorem some_full_bucket_tail {m B : ℕ} [NeZero B] (t : ℕ) :
    uprob (fun φ : Fin m → Fin B => ∃ b : Fin B, t < Buckets.load φ b) ≤
      (B : ℝ) * ((Nat.choose m (t + 1) : ℝ) / (B : ℝ) ^ (t + 1)) := by
  simpa only [Buckets.load_eq, Finset.inter_univ, Finset.card_univ, Fintype.card_fin]
    using (some_bucket_tail (Finset.univ : Finset (Fin m)) t)

end TCSlib.Cryptography.Obfuscation.StructuredSeed.Internal
