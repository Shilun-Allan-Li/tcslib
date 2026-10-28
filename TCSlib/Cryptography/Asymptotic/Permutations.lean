/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.Sampling
import Mathlib.Algebra.Group.End
import Mathlib.Data.Nat.Size
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Rejection-sampled random permutations

The permutation sampler of the Pass–shelat campaign (foundation decision D10): Fisher–Yates
with offsets drawn by the rejection sampler `rejectionSample` of `Asymptotic/Sampling.lean`,
one independent block of coins per position. `permFromCoins n k T` uses `T` trials of `k`
bits for each of the `n` positions; conditioned on success it is a uniformly random
permutation of `Fin n` (`permFromCoins_uniform_of_some`), it fails with probability at most
`n (1 - 1/2^k)^T` (`uprob_permFromCoins_none_le`), and with any default on failure it is
`StatClose` to a uniform permutation within that term (`statClose_permFromCoins`, an instance
of `statClose_getD_of_uniform_of_some`). The campaign parameters are `permBits n = Nat.size n`
bits per trial (so `n ≤ 2^k ≤ 2n`) and `permTrials n = 2n²` trials per position, for which
the failure term has the closed form `n · 2^{-n}` (`uprob_permFromCoins_none_le_two_pow`,
`statClose_permFromCoins_two_pow`). These are the permutations `σ, π ← S_n` of the honest
parties and simulators of [PS10, Protocols 118.3 and 120.6] and the colour permutations of
[PS10, Protocol 127.5]; the string-level parties read their coins into the `n × T × k` table
by `coinTable` (`ZeroKnowledge/Encoding.lean`) and the consumers are stated in terms of the
parameters defined here. (The section was split off `Asymptotic/Sampling.lean` to respect the
file-size limit.)

**Deviation:** [PS10] samples `σ ← S_n` exactly, in expected polynomial time; here the
sampler is truncated to `permTrials n` trials per position and the protocol theorems carry
the explicit statistical term `n · 2^{-n}` (D10, deviations register #11 and #15).

**Deviation (from the frozen signature of `uprob_permFromCoins_none_le`):** the frozen bound
`n * (1/2)^T` is false for the frozen definition of `permFromCoins` (the position `i = n - 1`
samples `Fin 1` with `k` bits and fails with probability `(1 - 1/2^k)^T`; for `n = 3`, `k = 2`,
`T = 10` this is `(3/4)^10 > 3 · 2^{-10}`). The lemma is stated with the provable bound
`n * (1 - 1/2^k)^T`; per-trial failure `≤ 1/2` holds for a single `rejectionSample` with
`2^k ≤ 2 m` (`uprob_rejectionSample_none_le_half_pow`).

**Repair (run-3 audit P2-1):** the frozen parameters `permFromCoins n n n` of the
graph-isomorphism prover fail with probability at least `1 - n/2^n` (the last position has
range `1` and `n` bits per trial), so this file now owns the campaign parameters `permBits`,
`permTrials`, the general `StatClose` form `statClose_permFromCoins` and the closed form
`n · 2^{-n}` at those parameters; the consumers (`ZeroKnowledge/GraphIsomorphism.lean`:
`samplePerm`, `permCoinLen`, `permFailBound`; `ZeroKnowledge/Encoding.lean`:
`polyTimeComputable_encPermFromCoins`) are stated in terms of them.

## Main definitions

* `TCSlib.Cryptography.fisherYates`, `TCSlib.Cryptography.permFromCoins` — a permutation of
  `Fin n` from offsets, and from rejection-sampled offsets.
* `TCSlib.Cryptography.permBits`, `TCSlib.Cryptography.permTrials` — the campaign parameters
  of the permutation sampler (`Nat.size n` bits per trial, `2n²` trials per position).
* `TCSlib.Cryptography.liftSucc`, `TCSlib.Cryptography.fyOffsets` — the lift of a permutation of
  `Fin n` to `Fin (n + 1)` fixing `0`, and the finset of in-range offset tuples.

## Main results

* `TCSlib.Cryptography.fisherYates_succ`, `TCSlib.Cryptography.fisherYates_injOn`,
  `TCSlib.Cryptography.exists_fyOffsets` — the Fisher–Yates recursion through
  `Equiv.Perm.decomposeFin`, and the offset map is a bijection from the `n!` in-range offset
  tuples onto the permutations.
* `TCSlib.Cryptography.uprob_pi_forall_dep` — independent coordinates with position-dependent
  events multiply (the dependent form of `OneWay.uprob_pi_forall`).
* `TCSlib.Cryptography.permFromCoins_uniform_of_some`,
  `TCSlib.Cryptography.uprob_permFromCoins_none_le`,
  `TCSlib.Cryptography.statClose_permFromCoins` — the permutation sampler: uniform
  conditioned on success, failure at most `n (1 - 1/2^k)^T`, `StatClose` form.
* `TCSlib.Cryptography.le_two_pow_permBits`, `TCSlib.Cryptography.two_pow_permBits_le` —
  `n ≤ 2^{permBits n} ≤ 2n`.
* `TCSlib.Cryptography.uprob_permFromCoins_none_le_two_pow`,
  `TCSlib.Cryptography.statClose_permFromCoins_two_pow` — the closed form `n · 2^{-n}` at the
  campaign parameters.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Protocols 118.3 and 120.6, Theorem 122.3; §4.7 Protocol 127.5.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
-/

namespace TCSlib.Cryptography

open Finset

/-! ### Random permutations -/

/-- Fisher–Yates from offsets: `c i` is reduced modulo the number of remaining positions.
The permutation is `swap 0 (0 + c 0) ∘ swap 1 (1 + c 1) ∘ ⋯ ∘ swap (n-1) (n-1)` (the last
factor is applied first); the offset tuple `(c i mod (n - i))_i ↦ π` is a bijection from
`∏ Fin (n - i)` onto the permutations of `Fin n`. -/
def fisherYates (n : ℕ) (c : Fin n → ℕ) : Equiv.Perm (Fin n) :=
  (List.finRange n).foldr
    (fun i σ => Equiv.swap i ⟨(i + c i % (n - i)) % n,
      Nat.mod_lt _ (Nat.pos_of_ne_zero (by have := i.isLt; omega))⟩ * σ) 1

/-- A permutation from `n` rejection samplers (`T` trials of `k` bits for position `i`,
range `n - i`); uniform conditioned on `some`. The permutations `π ← S_n` of the prover and
simulator of [PS10, Protocol 120.6] and the colour permutations of [PS10, Protocol 127.5]. -/
def permFromCoins (n k T : ℕ) (b : Fin n → Fin T → Fin k → Bool) : Option (Equiv.Perm (Fin n)) :=
  if h : ∀ i : Fin n, (rejectionSample (n - i) k T (b i)).isSome then
    some (fisherYates n fun i => ((rejectionSample (n - i) k T (b i)).get (h i)).val)
  else none

/-- The permutation sampler fails exactly when some position's rejection sampler fails. -/
theorem permFromCoins_eq_none_iff (n k T : ℕ) (b : Fin n → Fin T → Fin k → Bool) :
    permFromCoins n k T b = none ↔ ∃ i : Fin n, rejectionSample (n - i) k T (b i) = none := by
  unfold permFromCoins
  split_ifs with h
  · simp only [false_iff, not_exists]
    intro i hi
    simpa [hi] using h i
  · simp only [true_iff]
    by_contra hc
    push_neg at hc
    exact h fun i => Option.isSome_iff_ne_none.2 (hc i)

/-! ### The Fisher–Yates offset map is a bijection -/

/-- The lift of a permutation of `Fin n` to `Fin (n + 1)` fixing `0`: `decomposeFin.symm (0, e)`,
with `liftSucc e 0 = 0` and `liftSucc e x.succ = (e x).succ`. -/
def liftSucc {n : ℕ} (e : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (n + 1)) :=
  Equiv.Perm.decomposeFin.symm (0, e)

/-- The lift fixes `0`. -/
@[simp] theorem liftSucc_zero {n : ℕ} (e : Equiv.Perm (Fin n)) : liftSucc e 0 = 0 := by
  simp [liftSucc, Equiv.Perm.decomposeFin_symm_apply_zero]

/-- The lift acts as `e` on successors. -/
@[simp] theorem liftSucc_succ {n : ℕ} (e : Equiv.Perm (Fin n)) (x : Fin n) :
    liftSucc e x.succ = (e x).succ := by
  simp [liftSucc, Equiv.Perm.decomposeFin_symm_apply_succ]

/-- The lift of the identity is the identity. -/
theorem liftSucc_one {n : ℕ} : liftSucc (1 : Equiv.Perm (Fin n)) = 1 := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x <;> simp

/-- The lift is multiplicative. -/
theorem liftSucc_mul {n : ℕ} (e e' : Equiv.Perm (Fin n)) :
    liftSucc (e * e') = liftSucc e * liftSucc e' := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x <;> simp [Equiv.Perm.mul_apply]

/-- The lift of a transposition is the transposition of the successors. -/
theorem liftSucc_swap {n : ℕ} (a b : Fin n) :
    liftSucc (Equiv.swap a b) = Equiv.swap a.succ b.succ := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · rw [liftSucc_zero, Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero a).symm
      (Fin.succ_ne_zero b).symm]
  · rw [liftSucc_succ, Equiv.swap_apply_def, Equiv.swap_apply_def]
    by_cases h1 : x = a
    · subst h1
      simp
    · by_cases h2 : x = b
      · subst h2
        simp [h1, Fin.succ_inj]
      · simp [h1, h2, Fin.succ_inj]

/-- `decomposeFin.symm (p, e)` is the transposition `(0 p)` after the lift of `e`. -/
theorem decomposeFin_symm_eq {n : ℕ} (p : Fin (n + 1)) (e : Equiv.Perm (Fin n)) :
    Equiv.Perm.decomposeFin.symm (p, e) = Equiv.swap 0 p * liftSucc e := by
  ext x
  refine Fin.cases ?_ (fun x => ?_) x
  · simp [Equiv.Perm.decomposeFin_symm_apply_zero, Equiv.Perm.mul_apply]
  · simp [Equiv.Perm.decomposeFin_symm_apply_succ, Equiv.Perm.mul_apply]

/-- Folding the lifted transpositions is the lift of the fold (`liftSucc` is multiplicative). -/
theorem foldr_swap_succ {n : ℕ} (s : Fin n → Fin n) : ∀ l : List (Fin n),
    l.foldr (fun i σ => Equiv.swap i.succ (s i).succ * σ) 1 =
      liftSucc (l.foldr (fun i σ => Equiv.swap i (s i) * σ) 1)
  | [] => liftSucc_one.symm
  | i :: l => by
    rw [List.foldr_cons, List.foldr_cons, liftSucc_mul, liftSucc_swap, foldr_swap_succ s l]

/-- **The Fisher–Yates recursion:** for in-range offsets (`c i < n + 1 - i`), the permutation on
`n + 1` positions is `decomposeFin.symm (c 0, fisherYates n (c ∘ succ))` — the transposition of
position `0` with `c 0` after the lifted permutation of the remaining positions.

**Proof sketch.** `List.finRange_succ` and `List.foldr_map` split off the factor at position `0`,
whose target is `c 0` (no modulus wraps). The factor at position `i.succ` is
`swap i.succ (i + 1 + c i.succ)`, the lift of the factor `swap i (i + c i.succ)` of
`fisherYates n (c ∘ succ)` (again no modulus wraps since `c i.succ < n - i`), so the remaining
fold is the lift of the inner fold (`foldr_swap_succ`), and `decomposeFin_symm_eq` assembles the
product. -/
theorem fisherYates_succ {n : ℕ} (c : Fin (n + 1) → ℕ) (hc : ∀ i, c i < n + 1 - i) :
    fisherYates (n + 1) c = Equiv.Perm.decomposeFin.symm
      (⟨c 0, by simpa using hc 0⟩, fisherYates n (fun i => c i.succ)) := by
  rw [decomposeFin_symm_eq]
  unfold fisherYates
  rw [List.finRange_succ, List.foldr_cons, List.foldr_map]
  congr 1
  · congr 1
    apply Fin.ext
    have h0 : c 0 < n + 1 := by simpa using hc 0
    simp only [Fin.val_zero, Nat.sub_zero, Nat.zero_add, Nat.mod_eq_of_lt h0]
  · rw [← foldr_swap_succ (fun i : Fin n =>
      (⟨(↑i + c i.succ % (n - ↑i)) % n, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
        have := i.isLt; omega))⟩ : Fin n))]
    congr 1
    funext i σ
    congr 2
    apply Fin.ext
    have h1 : c i.succ < n - i := by
      have := hc i.succ
      rwa [Fin.val_succ, Nat.add_sub_add_right] at this
    have h2 := i.isLt
    simp only [Fin.val_succ]
    rw [Nat.add_sub_add_right, Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- **The Fisher–Yates offset map is injective on in-range offsets:** two offset tuples with
`c i, c' i < n - i` giving the same permutation are equal.

**Proof sketch.** Induction on `n` through `fisherYates_succ`: `decomposeFin.symm` is injective,
so the first offsets agree and the permutations of the tails agree, and the induction
hypothesis (the tails are in range since `c i.succ < n + 1 - (i + 1) = n - i`) gives the rest
(`Fin.cases`). -/
theorem fisherYates_injOn : ∀ (n : ℕ) (c c' : Fin n → ℕ), (∀ i, c i < n - i) →
    (∀ i, c' i < n - i) → fisherYates n c = fisherYates n c' → c = c'
  | 0, _, _, _, _, _ => funext fun i => i.elim0
  | n + 1, c, c', hc, hc', h => by
    rw [fisherYates_succ c hc, fisherYates_succ c' hc'] at h
    have h' := Equiv.Perm.decomposeFin.symm.injective h
    rw [Prod.mk.injEq, Fin.mk.injEq] at h'
    obtain ⟨h0, htail⟩ := h'
    have hbound : ∀ (d : Fin (n + 1) → ℕ), (∀ i, d i < n + 1 - i) →
        ∀ i : Fin n, d i.succ < n - i := by
      intro d hd i
      have := hd i.succ
      rwa [Fin.val_succ, Nat.add_sub_add_right] at this
    have htail' := fisherYates_injOn n _ _ (hbound c hc) (hbound c' hc') htail
    funext i
    refine Fin.cases h0 (fun i => ?_) i
    exact congrFun htail' i

/-- The in-range offset tuples `(c i < n - i)_i` as a finset of `Fin n → ℕ`. -/
def fyOffsets (n : ℕ) : Finset (Fin n → ℕ) := Fintype.piFinset fun i : Fin n => Finset.range (n - i)

/-- Membership in `fyOffsets n`. -/
theorem mem_fyOffsets {n : ℕ} {c : Fin n → ℕ} : c ∈ fyOffsets n ↔ ∀ i, c i < n - i := by
  simp [fyOffsets, Fintype.mem_piFinset]

/-- `∏ i < n, (n - i) = n!`. -/
theorem prod_sub_eq_factorial : ∀ n : ℕ, ∏ i : Fin n, (n - (i : ℕ)) = n.factorial
  | 0 => by simp
  | n + 1 => by
    rw [Fin.prod_univ_succ, Nat.factorial_succ, ← prod_sub_eq_factorial n]
    simp only [Fin.val_zero, Nat.sub_zero, Fin.val_succ, Nat.add_sub_add_right]

/-- There are `n!` in-range offset tuples. -/
theorem card_fyOffsets (n : ℕ) : (fyOffsets n).card = n.factorial := by
  rw [fyOffsets, Fintype.card_piFinset]
  simp only [Finset.card_range]
  exact prod_sub_eq_factorial n

/-- **Every permutation is a Fisher–Yates permutation of a unique in-range offset tuple**
(existence half): the injective image (`fisherYates_injOn`) of the `n!` offset tuples
(`card_fyOffsets`) in the `n!` permutations (`Fintype.card_perm`) is everything
(`Finset.eq_univ_of_card`). -/
theorem exists_fyOffsets {n : ℕ} (π : Equiv.Perm (Fin n)) :
    ∃ c ∈ fyOffsets n, fisherYates n c = π := by
  have hinj : Set.InjOn (fisherYates n) (fyOffsets n) := fun c hc c' hc' h =>
    fisherYates_injOn n c c' (mem_fyOffsets.1 hc) (mem_fyOffsets.1 hc') h
  have hcard : ((fyOffsets n).image (fisherYates n)).card = Fintype.card (Equiv.Perm (Fin n)) := by
    rw [Finset.card_image_of_injOn hinj, card_fyOffsets, Fintype.card_perm, Fintype.card_fin]
  have hmem : π ∈ (fyOffsets n).image (fisherYates n) := by
    rw [Finset.eq_univ_of_card _ hcard]
    exact Finset.mem_univ _
  exact Finset.mem_image.1 hmem

/-- **Independent coordinates with position-dependent events multiply:** the probability that
every coordinate `i` of a uniform tuple satisfies its own event `P i` is the product of the
probabilities (the position-dependent form of `OneWay.uprob_pi_forall`: `Nat.card` of the
dependent product of subtypes, `Equiv.subtypePiEquivPi`, `Nat.card_pi`). -/
theorem uprob_pi_forall_dep {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (P : ι → α → Prop) :
    uprob (fun xs : ι → α => ∀ i, P i (xs i)) = ∏ i, uprob (P i) := by
  unfold uprob
  rw [Nat.card_congr (Equiv.subtypePiEquivPi (p := P)), Nat.card_pi, Fintype.card_fun,
    ← Finset.card_univ (α := ι), ← Finset.prod_const, Nat.cast_prod, Nat.cast_prod,
    Finset.prod_div_distrib]

/-- The event `{permFromCoins n k T b = some σ}` for `σ = fisherYates n c` with in-range offsets
`c` is the conjunction over the positions of `{rejectionSample (n - i) k T (b i) = some (c i)}`.

**Proof sketch.** Unfold `permFromCoins`. When every position succeeds, the output is
`fisherYates` of the sampled offsets, which are in range, so it equals `σ` iff the sampled
offsets are `c` (`fisherYates_injOn`), i.e. iff every position samples `c i`
(`Option.some_get`). When some position fails, the output is `none ≠ some σ` and the
conjunction fails at that position. -/
theorem permFromCoins_eq_some_iff {n k T : ℕ} (σ : Equiv.Perm (Fin n)) (c : Fin n → ℕ)
    (hc : ∀ i, c i < n - i) (hσ : fisherYates n c = σ) (b : Fin n → Fin T → Fin k → Bool) :
    permFromCoins n k T b = some σ ↔
      ∀ i : Fin n, rejectionSample (n - i) k T (b i) = some ⟨c i, hc i⟩ := by
  unfold permFromCoins
  split_ifs with h
  · rw [Option.some_inj]
    constructor
    · intro hfy
      have hd : (fun i : Fin n => ((rejectionSample (n - i) k T (b i)).get (h i)).val) = c :=
        fisherYates_injOn n _ _ (fun i => Fin.isLt _) hc (hfy.trans hσ.symm)
      intro i
      rw [← Option.some_get (h i)]
      congr 1
      exact Fin.ext (congrFun hd i)
    · intro hall
      rw [← hσ]
      congr 1
      funext i
      have := hall i
      rw [← Option.some_get (h i), Option.some_inj] at this
      rw [this]
  · constructor
    · intro h'
      exact absurd h' (by simp)
    · intro hall
      exact absurd (fun i => by rw [hall i]; rfl) h

/-- Conditioned on success, `permFromCoins` is a uniformly random permutation: any two
permutations are output with the same probability ([PS10, Protocol 120.6], "`π ← S_n`";
[PS10, Protocol 127.5], the random colour permutation).

**Proof sketch.** The positions use disjoint coins, so the events
`{rejectionSample (n - i) k T (b i) = some (c i)}` are independent across `i` (product form
of `OneWay.uprob_pi_forall` for position-dependent predicates: `Nat.card` of a dependent
product of subtypes, `Equiv.subtypePiEquivPi` and `Nat.card_pi`), each of probability
`q_i = (1 - f_i) / (n - i)` by `rejectionSample_uniform_of_some` and
`uprob_rejectionSample_none` (`0 < n - i ≤ 2^k` from `hk`). The offset map
`c ↦ fisherYates n c` is injective on `∏ Fin (n - i)`: by `List.finRange_succ` and
`List.foldr_map`, `fisherYates (n+1) c = Equiv.Perm.decomposeFin.symm (c 0, fisherYates n (c ∘ succ))`
(the factor at position `j.succ` is `swap j.succ b.succ`, the image of `swap j b` under
`e ↦ decomposeFin.symm (0, e)`, which is multiplicative by `decomposeFin_symm_apply_zero/succ`;
no modulus wraps since `c i < n - i`), so `decomposeFin` being a bijection gives `c 0 = c' 0`
and the induction hypothesis the rest. Every permutation is attained since
`Fintype.card (∀ i, Fin (n - i)) = n! = Fintype.card (Perm (Fin n))` (`Fin.prod_univ_succ`,
`Fintype.card_perm`, `Fintype.bijective_iff_injective_and_card`). Hence
`{permFromCoins = some π}` is the event `{∀ i, rejectionSample (n - i) k T (b i) = some (c_π i)}`
for the single offset tuple `c_π`, of probability `∏ q_i`, independent of `π`. (Proved through
`exists_fyOffsets`, `permFromCoins_eq_some_iff` and `uprob_pi_forall_dep` of the preceding
section.) -/
theorem permFromCoins_uniform_of_some (n k T : ℕ) (hk : n ≤ 2 ^ k) (π π' : Equiv.Perm (Fin n)) :
    uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = some π) =
      uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = some π') := by
  obtain ⟨c, hc, hcπ⟩ := exists_fyOffsets π
  obtain ⟨c', hc', hcπ'⟩ := exists_fyOffsets π'
  have hL := uprob_pi_forall_dep (ι := Fin n) (α := Fin T → Fin k → Bool)
    (fun i x => rejectionSample (n - i) k T x = some ⟨c i, (mem_fyOffsets.1 hc) i⟩)
  have hR := uprob_pi_forall_dep (ι := Fin n) (α := Fin T → Fin k → Bool)
    (fun i x => rejectionSample (n - i) k T x = some ⟨c' i, (mem_fyOffsets.1 hc') i⟩)
  rw [OneWay.uprob_congr (permFromCoins_eq_some_iff π c (mem_fyOffsets.1 hc) hcπ),
    OneWay.uprob_congr (permFromCoins_eq_some_iff π' c' (mem_fyOffsets.1 hc') hcπ'), hL, hR]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := i.isLt
  exact rejectionSample_uniform_of_some (n - i) k T (by omega) (by omega) _ _

/-- The permutation sampler fails with probability at most `n (1 - 1/2^k)^T` (union bound over
the `n` positions, each failing with probability `(1 - (n-i)/2^k)^T ≤ (1 - 1/2^k)^T`).

**Deviation (from the frozen signature):** the frozen bound `n * (1/2)^T` is false for the
frozen `permFromCoins` (position `n - 1` samples `Fin 1` with `k` bits: `n = 3`, `k = 2`,
`T = 10` gives failure `≥ (3/4)^10 > 3 · 2^{-10}`); the bound is corrected to
`n * (1 - 1/2^k)^T`, which is what the frozen definition supports.

**Proof sketch.** `permFromCoins_eq_none_iff`, the union bound `uprob_exists_le`, projection
of the uniform coin table to position `i` (`HardcoreBit.pushesUniform_eval`),
`uprob_rejectionSample_none` at range `n - i ≥ 1`, and monotonicity of `x ↦ x^T`. -/
theorem uprob_permFromCoins_none_le (n k T : ℕ) (hk : n ≤ 2 ^ k) :
    uprob (fun b : Fin n → Fin T → Fin k → Bool => permFromCoins n k T b = none) ≤
      n * (1 - 1 / 2 ^ k : ℝ) ^ T := by
  rw [OneWay.uprob_congr fun b => permFromCoins_eq_none_iff n k T b]
  have hex : ∀ b : Fin n → Fin T → Fin k → Bool,
      (∃ i : Fin n, rejectionSample (n - i) k T (b i) = none) ↔
        ∃ i ∈ (univ : Finset (Fin n)), rejectionSample (n - i) k T (b i) = none := by
    simp
  rw [OneWay.uprob_congr hex]
  refine (uprob_exists_le univ fun (i : Fin n) (b : Fin n → Fin T → Fin k → Bool) =>
    rejectionSample (n - i) k T (b i) = none).trans ?_
  have hterm : ∀ i : Fin n,
      uprob (fun b : Fin n → Fin T → Fin k → Bool => rejectionSample (n - i) k T (b i) = none) ≤
        (1 - 1 / 2 ^ k : ℝ) ^ T := by
    intro i
    have hi := i.isLt
    rw [(HardcoreBit.pushesUniform_eval i).uprob_eq
      (fun c : Fin T → Fin k → Bool => rejectionSample (n - i) k T c = none),
      uprob_rejectionSample_none _ _ _ (by omega) (by omega)]
    have h2k : (0 : ℝ) < 2 ^ k := by positivity
    apply pow_le_pow_left₀
    · rw [sub_nonneg, div_le_one h2k]
      exact_mod_cast (show n - (i : ℕ) ≤ 2 ^ k by omega)
    · gcongr
      exact_mod_cast (show 1 ≤ n - (i : ℕ) by omega)
  calc ∑ i : Fin n,
        uprob (fun b : Fin n → Fin T → Fin k → Bool => rejectionSample (n - i) k T (b i) = none)
      ≤ ∑ _i : Fin n, (1 - 1 / 2 ^ k : ℝ) ^ T := sum_le_sum fun i _ => hterm i
    _ = n * (1 - 1 / 2 ^ k : ℝ) ^ T := by
      rw [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Fallback-to-default form of the permutation sampler: with the identity (or any `d`) on
failure, `permFromCoins n k T` is within `n (1 - 1/2^k)^T` of a uniformly random permutation
of `Fin n` (D10; [PS10, Protocols 118.3, 120.6 and 127.5], "`σ ← S_n`"). The argument is
`statClose_getD_of_uniform_of_some` with `permFromCoins_uniform_of_some` and
`uprob_permFromCoins_none_le`.

**Repair (run-3 audit P2-1):** added; the consumers previously restated this argument. -/
theorem statClose_permFromCoins (n k T : ℕ) (hk : n ≤ 2 ^ k) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b : Fin n → Fin T → Fin k → Bool => (permFromCoins n k T b).getD d)
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (n * (1 - 1 / 2 ^ k : ℝ) ^ T) :=
  statClose_getD_of_uniform_of_some _ (permFromCoins_uniform_of_some n k T hk)
    (uprob_permFromCoins_none_le n k T hk) d

/-! ### The campaign parameters of the permutation sampler -/

/-- Bits per trial of the campaign's permutation sampler: `Nat.size n`, the least `k` with
`n < 2^k`, so that `n ≤ 2^k ≤ 2n` (`le_two_pow_permBits`, `two_pow_permBits_le`) and every
rejection trial of every position accepts with probability at least `1/(2n)` (D10).

**Repair (run-3 audit P2-1):** the frozen parameters (`n` bits per trial) accept a trial of
position `i` with probability `(n - i)/2^n`, so the frozen sampler `permFromCoins n n n`
failed with probability at least `1 - n/2^n`. -/
def permBits (n : ℕ) : ℕ := Nat.size n

/-- Trials per position of the campaign's permutation sampler: `2n²`, so that every position
fails with probability at most `(1 - 1/(2n))^{2n²} ≤ 2^{-n}` and the whole sampler with
probability at most `n · 2^{-n}` (`uprob_permFromCoins_none_le_two_pow`) (D10).

**Repair (run-3 audit P2-1):** the frozen `n` trials per position gave no negligible bound. -/
def permTrials (n : ℕ) : ℕ := 2 * n * n

/-- `n ≤ 2^{permBits n}`: the range of every position fits in the trial bits
(`Nat.lt_size_self`). -/
theorem le_two_pow_permBits (n : ℕ) : n ≤ 2 ^ permBits n := (Nat.lt_size_self n).le

/-- `permBits n ≤ n`: the sampler uses at most `n` bits per trial (`Nat.size_le`,
`Nat.lt_two_pow_self`), so its coin consumption `n · permTrials n · permBits n` is at most
`2n⁴`. -/
theorem permBits_le (n : ℕ) : permBits n ≤ n := Nat.size_le.2 Nat.lt_two_pow_self

/-- `2^{permBits n} ≤ 2n` for `n ≥ 1`: a trial of `permBits n` bits is at most twice the
range `n` (`Nat.size_le`: `2^{size n - 1} ≤ n`). -/
theorem two_pow_permBits_le {n : ℕ} (hn : 0 < n) : 2 ^ permBits n ≤ 2 * n := by
  have hs : 0 < Nat.size n := Nat.size_pos.2 hn
  have h : 2 ^ (Nat.size n - 1) ≤ n := by
    by_contra hc
    push_neg at hc
    have := Nat.size_le.2 hc
    omega
  calc 2 ^ permBits n = 2 * 2 ^ (Nat.size n - 1) := by
        rw [permBits, ← pow_succ']
        congr 1
        omega
    _ ≤ 2 * n := by omega

/-- At the campaign parameters the permutation sampler fails with probability at most
`n · 2^{-n}` (D10; the sampling term of [PS10, Propositions 118.4 and 120.7, Theorem 122.3]
in the campaign's statements).

**Proof sketch.** `uprob_permFromCoins_none_le` with `k = permBits n`, then
`1 - 1/2^k ≤ 1 - 1/(2n)` (`two_pow_permBits_le`) and
`(1 - 1/(2n))^{2n·n} = ((1 - 1/(2n))^{2n})^n ≤ (1/2)^n` (`one_sub_inv_pow_le_half`); the case
`n = 0` is `0 ≤ 0`. -/
theorem uprob_permFromCoins_none_le_two_pow (n : ℕ) :
    uprob (fun b : Fin n → Fin (permTrials n) → Fin (permBits n) → Bool =>
        permFromCoins n (permBits n) (permTrials n) b = none) ≤ n * (2 : ℝ)⁻¹ ^ n := by
  refine (uprob_permFromCoins_none_le n _ _ (le_two_pow_permBits n)).trans ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg n)
  have h2k : (2 : ℝ) ^ permBits n ≤ 2 * n := by exact_mod_cast two_pow_permBits_le hn
  have hpos : (0 : ℝ) < 2 ^ permBits n := by positivity
  have hstep : (1 - 1 / 2 ^ permBits n : ℝ) ≤ 1 - 1 / ((2 * n : ℕ) : ℝ) := by
    have := one_div_le_one_div_of_le hpos h2k
    push_cast
    linarith
  have h0 : (0 : ℝ) ≤ 1 - 1 / 2 ^ permBits n := by
    rw [sub_nonneg, div_le_one hpos]
    exact one_le_pow₀ (by norm_num)
  have h0' : (0 : ℝ) ≤ 1 - 1 / ((2 * n : ℕ) : ℝ) := by
    rw [sub_nonneg, div_le_one (by positivity)]
    exact_mod_cast (by omega : 1 ≤ 2 * n)
  calc (1 - 1 / 2 ^ permBits n : ℝ) ^ permTrials n
      ≤ (1 - 1 / ((2 * n : ℕ) : ℝ)) ^ permTrials n := pow_le_pow_left₀ h0 hstep _
    _ = ((1 - 1 / ((2 * n : ℕ) : ℝ)) ^ (2 * n)) ^ n := by rw [← pow_mul, permTrials]
    _ ≤ (1 / 2) ^ n :=
        pow_le_pow_left₀ (pow_nonneg h0' _) (one_sub_inv_pow_le_half (2 * n) (by omega)) n
    _ = (2 : ℝ)⁻¹ ^ n := by rw [one_div]

/-- At the campaign parameters the permutation sampler, with any default on failure, is
within `n · 2^{-n}` of a uniformly random permutation of `Fin n` (D10): the statistical term
carried by the graph-isomorphism statements ([PS10, Propositions 118.4 and 120.7,
Theorem 122.3]). `statClose_getD_of_uniform_of_some` with `permFromCoins_uniform_of_some` and
`uprob_permFromCoins_none_le_two_pow`. -/
theorem statClose_permFromCoins_two_pow (n : ℕ) (d : Equiv.Perm (Fin n)) :
    StatClose (fun b : Fin n → Fin (permTrials n) → Fin (permBits n) → Bool =>
        (permFromCoins n (permBits n) (permTrials n) b).getD d)
      (id : Equiv.Perm (Fin n) → Equiv.Perm (Fin n)) (n * (2 : ℝ)⁻¹ ^ n) :=
  statClose_getD_of_uniform_of_some _
    (permFromCoins_uniform_of_some n _ _ (le_two_pow_permBits n))
    (uprob_permFromCoins_none_le_two_pow n) d

end TCSlib.Cryptography
