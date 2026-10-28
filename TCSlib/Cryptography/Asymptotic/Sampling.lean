/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.OneWayFunctions.Basic
import TCSlib.Cryptography.HardcoreBit.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Sampling devices: statistical closeness, rejection sampling, random permutations

The one sampling device of the Pass–shelat campaign (foundation decision D10). Experiments
are stated with *ideal* uniform distributions, exactly as in [PS10]; honest parties and
reductions, which only have uniform coin strings, sample these distributions by truncated
rejection sampling, and every theorem carries the explicit statistical term. The file is
concrete-layer only: no machines, one security parameter at a time.

* `StatClose X Y δ` — two samplers from uniform seeds are statistically `δ`-close: every
  test set has probabilities under the two laws differing by at most `δ` (the
  sup-over-test-sets form of the statistical distance, usable for samples in an infinite type
  such as `List Bool`). It is closed under post-processing (`StatClose.map`), products
  (`StatClose.prod`), composition (`StatClose.trans`) and reparametrisation of the seed by a
  uniform-preserving map (`StatClose.comp_pushesUniform`), and bounds every distinguishing
  advantage (`distAdv_le_of_statClose`) and, more generally, every success probability of an
  experiment with auxiliary coins (`StatClose.abs_uprob_sub_le_prod`) — the statistical-switch
  lemma C10 of the Chapter 2 inventory.
* `HardcoreBit.PushesUniform` from equal fibres (`pushesUniform_of_card_fiber`, lemma C5): a map
  all of whose fibres have the same size pushes uniform to uniform (`QR_N` sampling by squaring,
  [PS10, Corollary 60.6, Theorem 63.10]).
* `firstHit E xs` — the first of `T` draws satisfying `E`: uniform on `E` conditioned on
  existence, and no hit with probability `(1 - Pr[E])^T` (lemma C4, [PS10, Lemma 51.17]).
* `rejectionSample m k T` — `T` trials of `k` bits read as a number, the first one below `m`:
  uniform on `Fin m` conditioned on `some`, `none` with probability `(1 - m/2^k)^T`, and the
  total sampler obtained by falling back to a default is `StatClose` to uniform within that
  term. This is the uniform position of [PS10, Theorem 35.1] and the samplers of `Π_n`, `Z_q`,
  `Z_N^*` and `QR_N` of [PS10, §2.6–§2.12].
* `statClose_getD_of_uniform_of_some` — a sampler that is uniform conditioned on success,
  made total by a default, is `StatClose` to uniform within its failure probability (C4 in
  abstract form); `one_sub_inv_pow_le_half` — `(1 - 1/m)^m ≤ 1/2`, the dyadic form of
  "`(1 - 1/m)^m ≈ e^{-1}`" used for the closed forms of the failure terms.
* The permutation sampler `permFromCoins n k T` (Fisher–Yates with rejection-sampled
  offsets, the permutations of [PS10, Protocols 118.3, 120.6 and 127.5]) and the campaign
  parameters `permBits`, `permTrials` live in `Asymptotic/Permutations.lean`
  (file-size limit).

**Deviation:** [PS10] samples primes, residues and permutations exactly, in expected
polynomial time; here every such sampler is truncated to `T` trials and the experiments carry
an explicit statistical term (D10, deviations register #15).

**Repair (run-3 audit P2-1):** the general closeness lemma `statClose_getD_of_uniform_of_some`,
the seed reparametrisation `StatClose.comp_pushesUniform` and `one_sub_inv_pow_le_half` were
added for the permutation sampler, whose section moved to `Asymptotic/Permutations.lean`.

## Main definitions

* `TCSlib.Cryptography.StatClose` — statistical `δ`-closeness of two samplers.
* `TCSlib.Cryptography.bitsToNat`, `TCSlib.Cryptography.bitsEquiv` — a `k`-bit string as a
  number below `2^k`, and the resulting bijection with `Fin (2^k)`.
* `TCSlib.Cryptography.uniformFromBits`, `TCSlib.Cryptography.rejectionSample` — one rejection
  trial, and `T` trials.
* `TCSlib.Cryptography.firstHit` — the first of `T` draws satisfying a predicate.

## Main results

* `TCSlib.Cryptography.StatClose.abs_uprob_sub_le_prod`,
  `TCSlib.Cryptography.distAdv_le_of_statClose` — the statistical-switch lemma (C10).
* `TCSlib.Cryptography.StatClose.map`, `TCSlib.Cryptography.StatClose.prod`,
  `TCSlib.Cryptography.StatClose.trans`, `TCSlib.Cryptography.StatClose.comp_pushesUniform`
  — closure properties.
* `TCSlib.Cryptography.pushesUniform_of_card_fiber` — equal fibres push uniform to uniform (C5).
* `TCSlib.Cryptography.firstHit_uniform_of_some`, `TCSlib.Cryptography.uprob_firstHit_none`,
  `TCSlib.Cryptography.statClose_firstHit` — the first hit is uniform (C4).
* `TCSlib.Cryptography.rejectionSample_uniform_of_some`,
  `TCSlib.Cryptography.uprob_rejectionSample_none`,
  `TCSlib.Cryptography.statClose_rejectionSample` — the rejection sampler.
* `TCSlib.Cryptography.statClose_getD_of_uniform_of_some` — a sampler that is uniform
  conditioned on success, made total by a default, is close to uniform within its failure
  probability (C4 in abstract form).
* `TCSlib.Cryptography.one_sub_inv_pow_le_half` — `(1 - 1/m)^m ≤ 1/2`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§2.4.2 Theorem 35.1; §2.6.5 Lemma 51.17; §2.12 Corollary 60.6 and Theorem 63.10;
  §4.4–§4.6 Protocols 120.6 and 127.5 for the permutation sampler of `Asymptotic/Permutations.lean`.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, Lemma 3.1 (statistical distance bounds every advantage).
-/

namespace TCSlib.Cryptography

open Finset

/-! ### Statistical closeness -/

/-- Two samplers `X : σ → γ` and `Y : τ → γ` from uniform seeds are *statistically
`δ`-close* when every test set `T ⊆ γ` has probabilities under the two sampled laws differing
by at most `δ`: the sup-over-test-sets form of the statistical distance, usable for samples in
an infinite type such as `List Bool`. The device of foundation decision D10: experiments use
ideal distributions, samplers approximate them within `StatClose` error
[PS10, §2.4.2 (the uniform position of Theorem 35.1), §4.3 (statistical zero-knowledge)]. -/
def StatClose {σ τ γ : Type*} [Fintype σ] [Fintype τ] (X : σ → γ) (Y : τ → γ) (δ : ℝ) : Prop :=
  ∀ T : γ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ

section StatClose

variable {σ τ υ γ γ' : Type*} [Fintype σ] [Fintype τ] [Fintype υ]

/-- Unfolding: for a `δ`-close pair the probability of any test set moves by at most `δ`. -/
theorem StatClose.abs_uprob_sub_le {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ)
    (T : γ → Prop) : |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ :=
  h T

/-- One-sided form: the probability of a test set under `X` is at most its probability under
`Y` plus `δ`. -/
theorem StatClose.uprob_le_add {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ)
    (T : γ → Prop) : uprob (fun s => T (X s)) ≤ uprob (fun t => T (Y t)) + δ := by
  linarith [(abs_le.1 (h T)).2]

/-- A closeness bound is nonnegative. -/
theorem StatClose.nonneg {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ) : 0 ≤ δ :=
  (abs_nonneg _).trans (h fun _ => True)

/-- A sampler is `0`-close to itself. -/
theorem StatClose.refl (X : σ → γ) : StatClose X X 0 := fun _ => by
  rw [sub_self, abs_zero]

/-- Closeness is symmetric. -/
theorem StatClose.symm {X : σ → γ} {Y : τ → γ} {δ : ℝ} (h : StatClose X Y δ) :
    StatClose Y X δ := fun T => by
  rw [abs_sub_comm]
  exact h T

/-- A closeness bound may be weakened. -/
theorem StatClose.mono {X : σ → γ} {Y : τ → γ} {δ δ' : ℝ} (h : StatClose X Y δ) (hδ : δ ≤ δ') :
    StatClose X Y δ' := fun T => (h T).trans hδ

/-- Closeness bounds add along a chain (triangle inequality). -/
theorem StatClose.trans {X : σ → γ} {Y : τ → γ} {Z : υ → γ} {δ δ' : ℝ}
    (h : StatClose X Y δ) (h' : StatClose Y Z δ') : StatClose X Z (δ + δ') := fun T =>
  (abs_sub_le _ _ _).trans (add_le_add (h T) (h' T))

/-- Post-processing both samplers by the same function preserves closeness: the test set `T`
for the images is the test set `T ∘ g` for the sources (statistical-switch lemma C10,
first half). -/
theorem StatClose.map {σ τ γ γ' : Type*} [Fintype σ] [Fintype τ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (g : γ → γ') : StatClose (fun s => g (X s)) (fun t => g (Y t)) δ :=
  fun T => h fun c => T (g c)

/-- Relabelling the seed space of the first sampler by a bijection preserves closeness. -/
theorem StatClose.comp_equiv_left {σ' : Type*} [Fintype σ'] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (e : σ' ≃ σ) : StatClose (fun s => X (e s)) Y δ := fun T => by
  rw [uprob_comp_equiv e (fun s => T (X s))]
  exact h T

/-- Relabelling the seed space of the second sampler by a bijection preserves closeness. -/
theorem StatClose.comp_equiv_right {τ' : Type*} [Fintype τ'] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (e : τ' ≃ τ) : StatClose X (fun t => Y (e t)) δ := fun T => by
  rw [uprob_comp_equiv e (fun t => T (Y t))]
  exact h T

/-- A map pushing uniform to uniform is `0`-close to the identity sampler: an exact sampler
(for example squaring onto `QR_N`, lemma C5) has no statistical term. -/
theorem statClose_of_pushesUniform {Ω : Type*} [Fintype Ω] [Fintype γ] {π : Ω → γ}
    (h : HardcoreBit.PushesUniform π) : StatClose π (id : γ → γ) 0 := fun T => by
  rw [h.uprob_eq T]
  simp

/-- Precomposing the first sampler with a map that pushes uniform to uniform (for example
reading a party's random tape as a coin table, `pushesUniform_coinTable`) preserves
closeness: the law of `X ∘ π` is the law of `X`.

**Repair (run-3 audit P2-1):** added for the string-level permutation samplers. -/
theorem StatClose.comp_pushesUniform {Ω : Type*} [Fintype Ω] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) {π : Ω → σ} (hπ : HardcoreBit.PushesUniform π) :
    StatClose (fun ω => X (π ω)) Y δ := fun T => by
  rw [hπ.uprob_eq (fun s => T (X s))]
  exact h T

/-- Averages of pointwise `c`-close functions are `c`-close (`0 ≤ c` covers the empty type). -/
private theorem abs_uexp_sub_le {α : Type*} [Fintype α] {f g : α → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ a, |f a - g a| ≤ c) : |uexp f - uexp g| ≤ c := by
  rw [← HardcoreBit.uexp_sub]
  unfold uexp
  rcases Nat.eq_zero_or_pos (Fintype.card α) with h0 | hpos
  · rw [h0]
    simpa using hc
  · have hc' : (0 : ℝ) < Fintype.card α := by exact_mod_cast hpos
    rw [abs_div, abs_of_pos hc', div_le_iff₀ hc']
    calc |∑ a, (f a - g a)| ≤ ∑ a, |f a - g a| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _a : α, c := Finset.sum_le_sum fun a _ => h a
      _ = c * Fintype.card α := by rw [sum_const, card_univ, nsmul_eq_mul, mul_comm]

/-- The statistical-switch lemma (C10 of the Chapter 2 inventory): replacing a sampler by a
`δ`-close one changes the success probability of any experiment that also uses independent
auxiliary coins `r : ρ` by at most `δ`. [Gar26, Lemma 3.1] in the sup-over-test-sets form.

**Proof sketch.** Average over the coins `r` (`uprob_prod` after swapping the coordinates):
for fixed `r` the event is the test set `P · r`, whose probability moves by at most `δ`
(`h`); the absolute value of an average is at most the average of the absolute values. -/
theorem StatClose.abs_uprob_sub_le_prod {ρ : Type*} [Fintype ρ] {X : σ → γ} {Y : τ → γ} {δ : ℝ}
    (h : StatClose X Y δ) (P : γ → ρ → Prop) :
    |uprob (fun z : σ × ρ => P (X z.1) z.2) - uprob (fun z : τ × ρ => P (Y z.1) z.2)| ≤ δ := by
  have e1 := uprob_comp_equiv (Equiv.prodComm ρ σ) (fun z : σ × ρ => P (X z.1) z.2)
  have e2 := uprob_comp_equiv (Equiv.prodComm ρ τ) (fun z : τ × ρ => P (Y z.1) z.2)
  rw [← e1, ← e2, uprob_prod, uprob_prod]
  exact abs_uexp_sub_le h.nonneg fun r => h fun g => P g r

/-- The distinguishing advantage of any distinguisher `D` (with its own coins) between two
`δ`-close samplers is at most `δ`: the computational counterpart of the statistical
distance bound `distAdv_le_statDist` [Gar26, Lemma 3.1], in the form used by every
"replace the ideal sampler by the rejection sampler" step of the campaign (C10). -/
theorem distAdv_le_of_statClose {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ]
    (X : σ → γ) (Y : τ → γ) {δ : ℝ} (h : StatClose X Y δ) (D : γ → ρ → Bool) :
    distAdv X Y D ≤ δ := by
  unfold distAdv acceptProb
  exact h.abs_uprob_sub_le_prod fun g r => D g r = true

/-- Closeness bounds add under independent products: if `X` is `δ`-close to `X'` and `Y` is
`δ'`-close to `Y'` then the pair sampler `(X, Y)` is `(δ + δ')`-close to `(X', Y')`.

**Proof sketch.** Hybrid `(X', Y)`: the first switch `(X, Y) → (X', Y)` is
`StatClose.abs_uprob_sub_le_prod` for `X, X'` with the second coordinate as auxiliary coins;
the second switch `(X', Y) → (X', Y')` is the same lemma for `Y, Y'` after swapping the
coordinates; conclude by the triangle inequality. -/
theorem StatClose.prod {σ σ' τ τ' γ γ' : Type*} [Fintype σ] [Fintype σ'] [Fintype τ] [Fintype τ']
    {X : σ → γ} {X' : τ → γ} {Y : σ' → γ'} {Y' : τ' → γ'} {δ δ' : ℝ}
    (h : StatClose X X' δ) (h' : StatClose Y Y' δ') :
    StatClose (fun z : σ × σ' => (X z.1, Y z.2)) (fun z : τ × τ' => (X' z.1, Y' z.2)) (δ + δ') := by
  intro T
  have h1 := h.abs_uprob_sub_le_prod fun g s' => T (g, Y s')
  have h2 := h'.abs_uprob_sub_le_prod fun g t => T (X' t, g)
  rw [← uprob_comp_equiv (Equiv.prodComm τ σ') (fun z : σ' × τ => T (X' z.2, Y z.1)),
    ← uprob_comp_equiv (Equiv.prodComm τ τ') (fun z : τ' × τ => T (X' z.2, Y' z.1))] at h2
  exact (abs_sub_le _ (uprob fun z : τ × σ' => T (X' z.1, Y z.2)) _).trans (add_le_add h1 h2)

end StatClose

/-! ### Equal fibres push uniform to uniform (C5) -/

/-- A map all of whose fibres have the same positive size `c` pushes the uniform distribution
forward to the uniform distribution (lemma C5 of the Chapter 2 inventory): sampling `QR_N` by
squaring a uniform unit, the squaring map being `4`-to-`1` on `Z_N^*` for `N = pq`
[PS10, Corollary 60.6, Theorem 63.10 (3)].

**Proof sketch.** Group the sum of `F ∘ π` by fibres: every fibre contributes `c · F g`, so
`∑ F ∘ π = c ∑ F` and `|Ω| = c |γ|`; the factor `c` cancels in the average. -/
theorem pushesUniform_of_card_fiber {Ω γ : Type*} [Fintype Ω] [Fintype γ] [DecidableEq γ]
    (π : Ω → γ) {c : ℕ} (hc : 0 < c)
    (hfib : ∀ g : γ, (univ.filter fun ω => π ω = g).card = c) : HardcoreBit.PushesUniform π := by
  intro F
  have hsum : ∑ ω, F (π ω) = (c : ℝ) * ∑ g, F g := by
    rw [← Finset.sum_fiberwise' univ π F, mul_sum]
    refine sum_congr rfl fun g _ => ?_
    rw [sum_const, nsmul_eq_mul, hfib]
  have hcard : Fintype.card Ω = c * Fintype.card γ := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := π) (t := univ) (fun _ _ => mem_univ _)]
    simp only [hfib, sum_const, card_univ, smul_eq_mul, mul_comm]
  have hpos : (c : ℝ) ≠ 0 := by exact_mod_cast hc.ne'
  simp only [uexp, hsum, hcard, Nat.cast_mul]
  rw [mul_div_mul_left _ _ hpos]

/-- Pigeonhole for fibres: if every fibre of `π` has at most `c` elements and the domain has
exactly `c` times as many elements as the codomain, then every fibre has exactly `c`
elements (the counting form of "`4`-to-`1`" in [PS10, Corollary 60.6]).

**Proof sketch.** `|Ω| = ∑_g |π⁻¹ g|`; a single fibre below `c` makes the sum below `c |γ|`. -/
theorem card_fiber_eq_of_le {Ω γ : Type*} [Fintype Ω] [Fintype γ] [DecidableEq γ] (π : Ω → γ)
    {c : ℕ} (hle : ∀ g : γ, (univ.filter fun ω => π ω = g).card ≤ c)
    (hcard : Fintype.card Ω = c * Fintype.card γ) (g : γ) :
    (univ.filter fun ω => π ω = g).card = c := by
  by_contra hne
  have hlt : (univ.filter fun ω => π ω = g).card < c := lt_of_le_of_ne (hle g) hne
  have h1 : Fintype.card Ω = ∑ g, (univ.filter fun ω => π ω = g).card := by
    rw [← card_univ, card_eq_sum_card_fiberwise (f := π) (t := univ) (fun _ _ => mem_univ _)]
  have h2 : ∑ g, (univ.filter fun ω => π ω = g).card < ∑ _g : γ, c :=
    sum_lt_sum (fun g _ => hle g) ⟨g, mem_univ _, hlt⟩
  rw [sum_const, card_univ, smul_eq_mul, mul_comm] at h2
  omega

/-- The `4`-to-`1` form of C5: fibres of size at most `c` and `|Ω| = c |γ|` give a map pushing
uniform to uniform. -/
theorem pushesUniform_of_card_fiber_le {Ω γ : Type*} [Fintype Ω] [Fintype γ] [DecidableEq γ]
    (π : Ω → γ) {c : ℕ} (hc : 0 < c) (hle : ∀ g : γ, (univ.filter fun ω => π ω = g).card ≤ c)
    (hcard : Fintype.card Ω = c * Fintype.card γ) : HardcoreBit.PushesUniform π :=
  pushesUniform_of_card_fiber π hc (card_fiber_eq_of_le π hle hcard)

/-! ### Bit strings as numbers -/

/-- The number with the given binary digits (most significant first). -/
def bitsToNat {k : ℕ} (b : Fin k → Bool) : ℕ :=
  (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0

/-- The digit fold with an arbitrary accumulator `a` contributes `a · 2^{|l|}`. -/
private theorem foldl_bits_eq (l : List Bool) (a : ℕ) :
    l.foldl (fun a c => 2 * a + (if c then 1 else 0)) a =
      a * 2 ^ l.length + l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := by
  induction l generalizing a with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, List.foldl_cons, ih, ih (2 * 0 + _), List.length_cons, pow_succ]
    ring

/-- The number read from `l` is below `2^{|l|}`. -/
private theorem listToNat_lt (l : List Bool) :
    l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 < 2 ^ l.length := by
  induction l with
  | nil => simp
  | cons c l ih =>
    rw [List.foldl_cons, foldl_bits_eq, List.length_cons, pow_succ]
    cases c <;> simp <;> omega

/-- Lists of the same length reading as the same number are equal. -/
private theorem listToNat_inj : ∀ (l l' : List Bool), l.length = l'.length →
    l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 =
      l'.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 → l = l'
  | [], [], _, _ => rfl
  | c :: l, c' :: l', hlen, heq => by
    rw [List.foldl_cons, List.foldl_cons, foldl_bits_eq, foldl_bits_eq (a := 2 * 0 + _)] at heq
    have hlen' : l.length = l'.length := by simpa using hlen
    have h1 := listToNat_lt l
    have h2 := listToNat_lt l'
    rw [hlen'] at heq h1
    obtain ⟨hc, hl⟩ : c = c' ∧ l.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 =
        l'.foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := by
      cases c <;> cases c' <;> simp at heq ⊢ <;> omega
    subst hc
    rw [listToNat_inj l l' hlen' hl]

/-- A `k`-bit string reads as a number below `2^k`. -/
theorem bitsToNat_lt {k : ℕ} (b : Fin k → Bool) : bitsToNat b < 2 ^ k := by
  have := listToNat_lt (List.ofFn b)
  rwa [List.length_ofFn] at this

/-- Reading `k`-bit strings as numbers is injective. -/
theorem bitsToNat_injective {k : ℕ} : Function.Injective (bitsToNat (k := k)) := fun b b' h =>
  List.ofFn_injective (listToNat_inj _ _ (by simp) h)

/-- The bijection between `k`-bit strings and `Fin (2^k)` given by `bitsToNat`: a uniform
`k`-bit string is a uniform number below `2^k`. -/
noncomputable def bitsEquiv (k : ℕ) : (Fin k → Bool) ≃ Fin (2 ^ k) :=
  Equiv.ofBijective (fun b => ⟨bitsToNat b, bitsToNat_lt b⟩)
    ((Fintype.bijective_iff_injective_and_card _).2
      ⟨fun b b' h => bitsToNat_injective (by simpa using congrArg Fin.val h), by simp⟩)

/-- The value of `bitsEquiv` is `bitsToNat`. -/
@[simp] theorem bitsEquiv_val {k : ℕ} (b : Fin k → Bool) : (bitsEquiv k b).val = bitsToNat b :=
  rfl

/-- A uniform `k`-bit string reads as a number below `m ≤ 2^k` with probability `m / 2^k`.

**Proof sketch.** Transport along `bitsEquiv` to the uniform distribution on `Fin (2^k)`,
where the event `{x < m}` has exactly `m` elements. -/
theorem uprob_bitsToNat_lt {m k : ℕ} (hk : m ≤ 2 ^ k) :
    uprob (fun b : Fin k → Bool => bitsToNat b < m) = m / 2 ^ k := by
  let e : {x : Fin (2 ^ k) // x.val < m} ≃ Fin m :=
    { toFun := fun x => ⟨x.1.val, x.2⟩
      invFun := fun y => ⟨⟨y.val, lt_of_lt_of_le y.2 hk⟩, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [show (fun b : Fin k → Bool => bitsToNat b < m) = fun b => (bitsEquiv k b).val < m from rfl,
    uprob_comp_equiv (bitsEquiv k) (fun x : Fin (2 ^ k) => x.val < m), uprob, Fintype.card_fin,
    Nat.card_congr e, Nat.card_eq_fintype_card, Fintype.card_fin]
  push_cast
  rfl

/-- One rejection trial: `k` bits read as a number, accepted iff below `m`. -/
def uniformFromBits (m k : ℕ) (b : Fin k → Bool) : Option (Fin m) :=
  if h : bitsToNat b < m then some ⟨_, h⟩ else none

/-- A trial yields `i` exactly when the bits read as `i`. -/
theorem uniformFromBits_eq_some_iff {m k : ℕ} (b : Fin k → Bool) (i : Fin m) :
    uniformFromBits m k b = some i ↔ bitsToNat b = i.val := by
  unfold uniformFromBits
  split_ifs with h
  · simp [Fin.ext_iff]
  · simp only [false_iff]
    exact fun h' => h (h' ▸ i.isLt)

/-- A trial fails exactly when the bits read as a number `≥ m`. -/
theorem uniformFromBits_eq_none_iff {m k : ℕ} (b : Fin k → Bool) :
    uniformFromBits m k b = none ↔ m ≤ bitsToNat b := by
  unfold uniformFromBits
  split_ifs with h
  · simp [h]
  · simp only [true_iff]
    exact not_lt.1 h

/-- Each value `i : Fin m` is hit by one trial with probability `1 / 2^k` (for `m ≤ 2^k`). -/
theorem uprob_uniformFromBits_eq_some {m k : ℕ} (hk : m ≤ 2 ^ k) (i : Fin m) :
    uprob (fun b : Fin k → Bool => uniformFromBits m k b = some i) = 1 / 2 ^ k := by
  have key := uprob_comp_equiv (bitsEquiv k)
    (fun x : Fin (2 ^ k) => x = ⟨i.val, lt_of_lt_of_le i.2 hk⟩)
  rw [OneWay.uprob_eq_one_div_card, Fintype.card_fin] at key
  have hiff : ∀ b : Fin k → Bool,
      uniformFromBits m k b = some i ↔ bitsEquiv k b = ⟨i.val, lt_of_lt_of_le i.2 hk⟩ := by
    intro b
    rw [uniformFromBits_eq_some_iff, Fin.ext_iff, bitsEquiv_val]
  rw [OneWay.uprob_congr hiff, key]
  push_cast
  rfl

/-- One trial fails with probability `1 - m / 2^k` (for `m ≤ 2^k`). -/
theorem uprob_uniformFromBits_none {m k : ℕ} (hk : m ≤ 2 ^ k) :
    uprob (fun b : Fin k → Bool => uniformFromBits m k b = none) = 1 - m / 2 ^ k := by
  rw [OneWay.uprob_congr fun b => (uniformFromBits_eq_none_iff b).trans not_lt.symm, uprob_not,
    uprob_bitsToNat_lt hk]

/-- Partition of an event by the value of a map: the probability that `f ω` satisfies `S` is
the sum over `b ∈ S` of the probabilities of the fibres `{f = b}`. -/
theorem uprob_comp_eq_sum_fiber {Ω β : Type*} [Fintype Ω] [Fintype β] [DecidableEq β] (f : Ω → β)
    (S : β → Prop) [DecidablePred S] :
    uprob (fun ω => S (f ω)) = ∑ b ∈ univ.filter S, uprob (fun ω => f ω = b) := by
  simp_rw [uprob_eq_card_filter, ← sum_div]
  congr 1
  rw [card_eq_sum_card_fiberwise (f := f) (s := univ.filter fun ω => S (f ω))
    (t := univ.filter S) (fun ω hω => by simpa using hω)]
  push_cast
  refine sum_congr rfl fun b hb => ?_
  have : (univ.filter fun ω => S (f ω)).filter (fun ω => f ω = b) =
      univ.filter fun ω => f ω = b := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, and_iff_right_iff_imp]
    intro h
    rw [h]
    exact (mem_filter.1 hb).2
  rw [this]

/-! ### The first hit of independent draws (C4) -/

/-- The first of the `T` draws `xs 0, …, xs (T-1)` satisfying `E`, if any: the general form of
the rejection sampler (lemma C4 of the Chapter 2 inventory; `SamplePrime`
[PS10, Algorithm 50.16] is `firstHit Prime` on `n`-bit numbers). -/
def firstHit {α : Type*} (E : α → Prop) [DecidablePred E] {T : ℕ} (xs : Fin T → α) : Option α :=
  (List.finRange T).findSome? fun t => if E (xs t) then some (xs t) else none

section FirstHit

variable {α : Type*} (E : α → Prop) [DecidablePred E] {T : ℕ}

/-- No hit exactly when no draw satisfies `E`. -/
theorem firstHit_eq_none_iff (xs : Fin T → α) : firstHit E xs = none ↔ ∀ t, ¬ E (xs t) := by
  unfold firstHit
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- A hit satisfies `E`. -/
theorem firstHit_eq_some_imp {xs : Fin T → α} {a : α} (h : firstHit E xs = some a) : E a := by
  unfold firstHit at h
  rw [List.findSome?_eq_some_iff] at h
  obtain ⟨_, t, _, _, ht, _⟩ := h
  by_cases hE : E (xs t)
  · rw [if_pos hE, Option.some.injEq] at ht
    exact ht ▸ hE
  · rw [if_neg hE] at ht
    exact absurd ht (Option.noConfusion)

variable [Fintype α]

/-- `T` independent uniform draws all miss `E` with probability `(1 - Pr[E])^T`
(C4, the failure probability of `SamplePrime` [PS10, Lemma 51.17]). -/
theorem uprob_firstHit_none [Nonempty α] (T : ℕ) :
    uprob (fun xs : Fin T → α => firstHit E xs = none) = (1 - uprob E) ^ T := by
  rw [OneWay.uprob_congr fun xs => firstHit_eq_none_iff E xs,
    OneWay.uprob_pi_forall fun a => ¬ E a, Fintype.card_fin, uprob_not]

/-- The first hit is uniform on `E` conditioned on existence: any two elements of `E` are the
first hit with the same probability (C4, [PS10, Lemma 51.17], "`p` is uniform in `Π_n`").

**Proof sketch.** The transposition `s = swap a a'` of `α` preserves `E` (both points lie in
`E`), hence commutes with `firstHit`: `firstHit E (s ∘ xs) = s <$> firstHit E xs`
(`List.map_findSome?`). Applying `s` coordinatewise is a bijection of the draw space
(`uprob_comp_equiv`), and it maps the event `{first hit = a}` onto `{first hit = a'}`. -/
theorem firstHit_uniform_of_some [DecidableEq α] (T : ℕ) {a a' : α} (ha : E a) (ha' : E a') :
    uprob (fun xs : Fin T → α => firstHit E xs = some a) =
      uprob (fun xs : Fin T → α => firstHit E xs = some a') := by
  have hE : ∀ x, E (Equiv.swap a a' x) ↔ E x := by
    intro x
    by_cases hx : x = a
    · subst hx
      rw [Equiv.swap_apply_left]
      exact ⟨fun _ => ha, fun _ => ha'⟩
    by_cases hx' : x = a'
    · subst hx'
      rw [Equiv.swap_apply_right]
      exact ⟨fun _ => ha', fun _ => ha⟩
    rw [Equiv.swap_apply_of_ne_of_ne hx hx']
  have hmap : ∀ xs : Fin T → α,
      firstHit E (fun t => Equiv.swap a a' (xs t)) = (firstHit E xs).map (Equiv.swap a a') := by
    intro xs
    unfold firstHit
    rw [List.map_findSome?]
    congr 1
    funext t
    by_cases h : E (xs t)
    · simp [h, (hE _).2 h]
    · simp [h, mt (hE _).1 h]
  rw [← uprob_comp_equiv (Equiv.piCongrRight fun _ : Fin T => Equiv.swap a a')
    (fun xs => firstHit E xs = some a')]
  refine OneWay.uprob_congr fun xs => ?_
  show firstHit E xs = some a ↔ firstHit E (fun t => Equiv.swap a a' (xs t)) = some a'
  rw [hmap, Option.map_eq_some_iff]
  constructor
  · intro h
    exact ⟨a, h, Equiv.swap_apply_left a a'⟩
  · rintro ⟨x, hx, hxa⟩
    have hxa' : x = a :=
      (Equiv.swap a a').injective (hxa.trans (Equiv.swap_apply_left a a').symm)
    rw [← hxa']
    exact hx

/-- Falling back to a default element `d ∈ E` when no draw hits makes the first-hit sampler
a total sampler within `(1 - Pr[E])^T` of the uniform distribution on `E` (C4 in the form
consumed by the collections and `SamplePrime`, [PS10, Lemma 51.17]).

**Proof sketch.** Let `f = (1 - Pr[E])^T` be the no-hit probability (`uprob_firstHit_none`)
and `q` the common probability of `{first hit = a}` for `a ∈ E` (`firstHit_uniform_of_some`);
the events `{first hit = a}` (`a ∈ E`) and `{no hit}` partition the draw space, so
`|E| q + f = 1`. For a test set `S`, `Pr[getD d ∈ S] = |S ∩ E| q + [d ∈ S] f` and the ideal
probability is `|S ∩ E| / |E| = |S ∩ E| q + (|S ∩ E| / |E|) f`; both lie in
`[|S ∩ E| q, |S ∩ E| q + f]`, so they differ by at most `f`. Sub-obligations: additivity of
`uprob` over the fibres of `firstHit` (`uprob_eq_card_filter` and
`Finset.card_eq_sum_card_fiberwise`), `Fintype.sum_option`, and `uprob` on the subtype
`{a // E a}` as a count (`uprob_eq_card_filter`). -/
theorem statClose_firstHit [DecidableEq α] [Nonempty α] (T : ℕ) {d : α} (hd : E d) :
    StatClose (fun xs : Fin T → α => (firstHit E xs).getD d) (fun e : {a // E a} => (e : α))
      ((1 - uprob E) ^ T) := by
  classical
  intro S
  have hsome : ∀ a, E a → uprob (fun xs : Fin T → α => firstHit E xs = some a) =
      uprob (fun xs : Fin T → α => firstHit E xs = some d) :=
    fun a ha => firstHit_uniform_of_some E T ha hd
  have hnot : ∀ a, ¬ E a → uprob (fun xs : Fin T → α => firstHit E xs = some a) = 0 := by
    intro a ha
    rw [← uprob_false (α := Fin T → α)]
    exact OneWay.uprob_congr fun xs => ⟨fun h => ha (firstHit_eq_some_imp E h), False.elim⟩
  -- the law of `firstHit`: `none` with probability `f`, each `a ∈ E` with probability `q`
  have hdec : ∀ S' : Option α → Prop, uprob (fun xs : Fin T → α => S' (firstHit E xs)) =
      (if S' none then (1 - uprob E) ^ T else 0) +
        uprob (fun xs : Fin T → α => firstHit E xs = some d) *
          (univ.filter fun a => E a ∧ S' (some a)).card := by
    intro S'
    rw [uprob_comp_eq_sum_fiber (firstHit E) S', sum_filter, Fintype.sum_option,
      uprob_firstHit_none E T]
    congr 1
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hSa : S' (some a)
    · by_cases hEa : E a
      · simp [hSa, hEa, hsome a hEa]
      · simp [hSa, hEa, hnot a hEa]
    · simp [hSa]
  have h1 := hdec fun o => S (o.getD d)
  simp only [Option.getD_none, Option.getD_some] at h1
  have htot := hdec fun _ => True
  simp only [uprob_true, if_true, and_true] at htot
  have hideal : uprob (fun e : {a // E a} => S e.val) =
      ((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card := by
    rw [uprob, Nat.card_congr (Equiv.subtypeSubtypeEquivSubtypeInter E S), Nat.card_eq_fintype_card,
      Fintype.card_subtype, Fintype.card_subtype]
  rw [h1, hideal]
  -- arithmetic: with `N = |E|`, `M = |E ∩ S|`, `q N = 1 - f`, the difference is `f ([d ∈ S] - M/N)`
  have hN : (0 : ℝ) < (univ.filter E).card := by
    exact_mod_cast card_pos.2 ⟨d, by simpa using hd⟩
  have hMN : ((univ.filter fun a => E a ∧ S a).card : ℝ) ≤ (univ.filter E).card := by
    exact_mod_cast card_le_card fun a ha => by
      simp only [mem_filter, mem_univ, true_and] at ha ⊢
      exact ha.1
  have hf0 : (0 : ℝ) ≤ (1 - uprob E) ^ T := pow_nonneg (by linarith [uprob_le_one E]) T
  have hq : uprob (fun xs : Fin T → α => firstHit E xs = some d) =
      (1 - (1 - uprob E) ^ T) / (univ.filter E).card := by
    rw [eq_div_iff hN.ne']
    linarith
  rw [hq]
  have hr0 : (0 : ℝ) ≤ ((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card :=
    div_nonneg (Nat.cast_nonneg _) hN.le
  have hr1 : ((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card ≤ 1 :=
    (div_le_one hN).2 hMN
  have hrw : (1 - (1 - uprob E) ^ T) / (univ.filter E).card *
      ((univ.filter fun a => E a ∧ S a).card : ℝ) =
      (1 - (1 - uprob E) ^ T) *
        (((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card) := by
    ring
  rw [hrw]
  generalize ((univ.filter fun a => E a ∧ S a).card : ℝ) / (univ.filter E).card = r at hr0 hr1 ⊢
  generalize (1 - uprob E) ^ T = f at hf0 ⊢
  by_cases hSd : S d
  · rw [if_pos hSd]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · rw [if_neg hSd]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

end FirstHit

/-! ### Rejection sampling of `Fin m` -/

/-- `T` rejection trials of `k` bits each; the first accepted value. Uniform on `Fin m`
conditioned on `some`; `none` with probability `(1 - m/2^k)^T`. The sampler of the uniform
position `i ∈ [m]` of [PS10, Theorem 35.1] and of the residues of [PS10, §2.6–§2.12]. -/
def rejectionSample (m k T : ℕ) (b : Fin T → Fin k → Bool) : Option (Fin m) :=
  (List.finRange T).findSome? fun t => uniformFromBits m k (b t)

/-- The rejection sampler fails exactly when every trial fails. -/
theorem rejectionSample_eq_none_iff (m k T : ℕ) (b : Fin T → Fin k → Bool) :
    rejectionSample m k T b = none ↔ ∀ t, uniformFromBits m k (b t) = none := by
  unfold rejectionSample
  rw [List.findSome?_eq_none_iff]
  simp [List.mem_finRange]

/-- The rejection sampler is the first hit of the event `{x < m}` among the `T` numbers read
from the trials (embedding `Fin m` into `Fin (2^k)`). -/
theorem map_rejectionSample_eq_firstHit {m k T : ℕ} (hk : m ≤ 2 ^ k) (b : Fin T → Fin k → Bool) :
    (rejectionSample m k T b).map (fun i : Fin m => (⟨i.val, lt_of_lt_of_le i.2 hk⟩ : Fin (2 ^ k))) =
      firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t)) := by
  unfold rejectionSample firstHit
  rw [List.map_findSome?]
  congr 1
  funext t
  simp only [Function.comp, uniformFromBits, bitsEquiv_val]
  split_ifs <;> rfl

/-- Lemma C4 for the rejection sampler: conditioned on success the output is uniform — any two
values of `Fin m` are output with the same probability ([PS10, Theorem 35.1], the uniform
position; [PS10, Lemma 51.17]).

**Proof sketch.** By `map_rejectionSample_eq_firstHit` the event `{output = i}` is the event
`{firstHit {x < m} = i}` for the numbers read from the trials; reading is a bijection of
each trial's bits onto `Fin (2^k)` (`bitsEquiv`, applied coordinatewise by
`Equiv.piCongrRight`), and `firstHit_uniform_of_some` gives the symmetry between `i` and
`j`. -/
theorem rejectionSample_uniform_of_some (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) (i j : Fin m) :
    uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = some i) =
      uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = some j) := by
  have _ := hm
  let toBig : Fin m → Fin (2 ^ k) := fun i => ⟨i.val, lt_of_lt_of_le i.2 hk⟩
  have hinj : Function.Injective toBig := fun x y h =>
    Fin.ext (show (toBig x).val = (toBig y).val from congrArg Fin.val h)
  have key : ∀ (b : Fin T → Fin k → Bool) (i : Fin m), rejectionSample m k T b = some i ↔
      firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t)) = some (toBig i) := by
    intro b i
    rw [← map_rejectionSample_eq_firstHit hk, Option.map_eq_some_iff]
    constructor
    · intro h
      exact ⟨i, h, rfl⟩
    · rintro ⟨x, hx, hxi⟩
      rw [hinj hxi] at hx
      exact hx
  have e : ∀ i : Fin m, uprob (fun b : Fin T → Fin k → Bool =>
      firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t)) = some (toBig i)) =
      uprob (fun xs : Fin T → Fin (2 ^ k) =>
        firstHit (fun x : Fin (2 ^ k) => x.val < m) xs = some (toBig i)) := fun i =>
    uprob_comp_equiv (Equiv.piCongrRight fun _ : Fin T => bitsEquiv k)
      (fun xs => firstHit (fun x : Fin (2 ^ k) => x.val < m) xs = some (toBig i))
  rw [OneWay.uprob_congr fun b => key b i, OneWay.uprob_congr fun b => key b j, e i, e j]
  exact firstHit_uniform_of_some _ T i.2 j.2

/-- The rejection sampler fails with probability exactly `(1 - m/2^k)^T` (C4, the no-hit
probability; [PS10, Lemma 51.17] with `Pr[E] = m/2^k`). -/
theorem uprob_rejectionSample_none (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) :
    uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = none) =
      (1 - (m : ℝ) / 2 ^ k) ^ T := by
  have _ := hm
  rw [OneWay.uprob_congr fun b => rejectionSample_eq_none_iff m k T b,
    OneWay.uprob_pi_forall fun c : Fin k → Bool => uniformFromBits m k c = none,
    Fintype.card_fin, uprob_uniformFromBits_none hk]

/-- With `k` chosen so that `2^k ≤ 2m` (the smallest `k` with `m ≤ 2^k`), every trial fails
with probability at most `1/2`, so `T` trials fail with probability at most `2^{-T}`: the
choice of `T = n` in the campaign's honest samplers. -/
theorem uprob_rejectionSample_none_le_half_pow (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k)
    (h2 : 2 ^ k ≤ 2 * m) :
    uprob (fun b : Fin T → Fin k → Bool => rejectionSample m k T b = none) ≤ (1 / 2 : ℝ) ^ T := by
  rw [uprob_rejectionSample_none m k T hm hk]
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hm' : (m : ℝ) ≤ 2 ^ k := by exact_mod_cast hk
  have h2' : (2 : ℝ) ^ k ≤ 2 * m := by exact_mod_cast h2
  apply pow_le_pow_left₀
  · rw [sub_nonneg, div_le_one h2k]
    exact hm'
  · have : (1 / 2 : ℝ) ≤ m / 2 ^ k := by
      rw [div_le_div_iff₀ (by norm_num) h2k]
      linarith
    linarith

/-- `(1 - 1/m)^m ≤ 1/2` for `m ≥ 1`: `m` trials each failing with probability `1 - 1/m`
all fail with probability at most `1/2` (the dyadic form of "`(1 - 1/m)^m ≈ e^{-1}`").

**Proof sketch.** Bernoulli's inequality `one_add_mul_le_pow` gives `(1 + 1/m)^m ≥ 2`, and
`(1 - 1/m)^m (1 + 1/m)^m = (1 - 1/m²)^m ≤ 1`, so `(1 - 1/m)^m ≤ 1/(1 + 1/m)^m ≤ 1/2`. -/
theorem one_sub_inv_pow_le_half (m : ℕ) (hm : 0 < m) : (1 - 1 / (m : ℝ)) ^ m ≤ 1 / 2 := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  set x : ℝ := 1 / m with hx
  have hx0 : 0 ≤ x := by positivity
  have hx1 : x ≤ 1 := by
    rw [hx, div_le_one hm']
    exact_mod_cast hm
  have hb : 1 + (m : ℝ) * x ≤ (1 + x) ^ m := one_add_mul_le_pow (by linarith) m
  have hmx : (m : ℝ) * x = 1 := by
    rw [hx]
    field_simp
  rw [hmx] at hb
  have hprod : (1 - x) ^ m * (1 + x) ^ m ≤ 1 := by
    rw [← mul_pow]
    have : (1 - x) * (1 + x) = 1 - x ^ 2 := by ring
    rw [this]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have hpos : (0 : ℝ) < (1 + x) ^ m := by positivity
  calc (1 - x) ^ m = (1 - x) ^ m * (1 + x) ^ m / (1 + x) ^ m := by field_simp
    _ ≤ 1 / (1 + x) ^ m := by gcongr
    _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)

/-- Fallback-to-default makes a total sampler within `(1 - m/2^k)^T` of uniform: the form of
C4 consumed by Theorem 35.1 (uniform position), the collections (`SampleClose`) and the
Chapter 4 simulators.

**Proof sketch.** Let `f = (1 - m/2^k)^T` (`uprob_rejectionSample_none`) and `q` the common
probability of `{output = i}` (`rejectionSample_uniform_of_some`); the `m + 1` events
`{output = i}`, `{output = none}` partition the coin space, so `m q + f = 1`. For a test set
`S ⊆ Fin m`, `Pr[getD d ∈ S] = |S| q + [d ∈ S] f` and `|S| / m = |S| q + (|S|/m) f`; both lie
in `[|S| q, |S| q + f]`. Alternatively: `map_rejectionSample_eq_firstHit`, the coordinatewise
bijection `bitsEquiv`, and `statClose_firstHit` on `Fin (2^k)` with `E = {x < m}`, transported
along the bijection `{x : Fin (2^k) // x < m} ≃ Fin m` (`StatClose.comp_equiv_right`,
`StatClose.map`). -/
theorem statClose_rejectionSample (m k T : ℕ) (hm : 0 < m) (hk : m ≤ 2 ^ k) (d : Fin m) :
    StatClose (fun b : Fin T → Fin k → Bool => (rejectionSample m k T b).getD d) (id : Fin m → Fin m)
      ((1 - (m : ℝ) / 2 ^ k) ^ T) := by
  have _ := hm
  let toBig : Fin m → Fin (2 ^ k) := fun i => ⟨i.val, lt_of_lt_of_le i.2 hk⟩
  let g : Fin (2 ^ k) → Fin m := fun x => if h : x.val < m then ⟨x.val, h⟩ else d
  let e : Fin m ≃ {x : Fin (2 ^ k) // x.val < m} :=
    { toFun := fun i => ⟨toBig i, i.2⟩
      invFun := fun x => ⟨x.1.val, x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hE : uprob (fun x : Fin (2 ^ k) => x.val < m) = m / 2 ^ k := by
    rw [← uprob_bitsToNat_lt hk, ← uprob_comp_equiv (bitsEquiv k) (fun x : Fin (2 ^ k) => x.val < m)]
    rfl
  have h := (((statClose_firstHit (fun x : Fin (2 ^ k) => x.val < m) T (d := toBig d) d.2).comp_equiv_left
    (Equiv.piCongrRight fun _ : Fin T => bitsEquiv k)).map g).comp_equiv_right e
  rw [hE] at h
  have h' : StatClose (fun b : Fin T → Fin k → Bool =>
      g ((firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t))).getD (toBig d)))
      (fun i : Fin m => g (toBig i)) ((1 - (m : ℝ) / 2 ^ k) ^ T) := h
  have hX : (fun b : Fin T → Fin k → Bool =>
      g ((firstHit (fun x : Fin (2 ^ k) => x.val < m) (fun t => bitsEquiv k (b t))).getD (toBig d))) =
      fun b => (rejectionSample m k T b).getD d := by
    funext b
    rw [← map_rejectionSample_eq_firstHit hk]
    cases rejectionSample m k T b with
    | none => simp [g, toBig, d.2]
    | some i => simp [g, i.2]
  have hY : (fun i : Fin m => g (toBig i)) = id := by
    funext i
    simp [g, toBig, i.2]
  rw [hX, hY] at h'
  exact h'

/-! ### Total samplers from samplers that are uniform conditioned on success -/

/-- A sampler `S : Ω → Option γ` that is uniform conditioned on success (any two values are
output with the same probability) and fails with probability at most `f`, made total by a
default `d`, is within `f` of the uniform distribution on `γ`: the common argument of
`statClose_firstHit`, `statClose_rejectionSample` and `statClose_permFromCoins` (lemma C4 in
its abstract form; [PS10, Lemma 51.17] for `SamplePrime`, [PS10, Protocol 120.6] for
`π ← S_n`).

**Repair (run-3 audit P2-1):** added so that the permutation sampler has a `StatClose` form
in this file instead of in each consumer.

**Proof sketch.** With `p = Pr[S = none]`, `q = Pr[S = some d]` (the common value of
`Pr[S = some a]`) and `G = |γ|`, the `G + 1` events `{S = some a}`, `{S = none}` partition the
seed space (`uprob_comp_eq_sum_fiber`, `Fintype.sum_option`), so `p + q G = 1`; for a test
set `T` with `M = |T|`, `Pr[getD d ∈ T] = [d ∈ T] p + q M` and `M / G = q M + (M / G) p`,
whose difference is `p ([d ∈ T] - M/G)`, of absolute value at most `p ≤ f`. -/
theorem statClose_getD_of_uniform_of_some {Ω γ : Type*} [Fintype Ω] [Nonempty Ω] [Fintype γ]
    [DecidableEq γ] (S : Ω → Option γ)
    (huni : ∀ a a' : γ, uprob (fun ω => S ω = some a) = uprob (fun ω => S ω = some a'))
    {f : ℝ} (hf : uprob (fun ω => S ω = none) ≤ f) (d : γ) :
    StatClose (fun ω => (S ω).getD d) (id : γ → γ) f := by
  classical
  intro T
  -- the law of `S`: `none` with probability `p`, each `a : γ` with the common probability `q`
  have hdec : ∀ S' : Option γ → Prop, uprob (fun ω => S' (S ω)) =
      (if S' none then uprob (fun ω => S ω = none) else 0) +
        uprob (fun ω => S ω = some d) * (univ.filter fun a => S' (some a)).card := by
    intro S'
    rw [uprob_comp_eq_sum_fiber S S', sum_filter, Fintype.sum_option]
    congr 1
    rw [mul_comm, ← nsmul_eq_mul, ← sum_const, sum_filter]
    refine sum_congr rfl fun a _ => ?_
    by_cases hSa : S' (some a)
    · simp [hSa, huni a d]
    · simp [hSa]
  have h1 := hdec fun o => T (o.getD d)
  simp only [Option.getD_none, Option.getD_some] at h1
  have htot := hdec fun _ => True
  simp only [uprob_true, if_true, filter_true, card_univ] at htot
  have hideal : uprob (fun a : γ => T (id a)) = ((univ.filter T).card : ℝ) / Fintype.card γ := by
    rw [uprob_eq_card_filter]
    rfl
  rw [h1, hideal]
  -- arithmetic: with `q G = 1 - p`, the difference is `p ([d ∈ T] - M/G)`
  have hG : (0 : ℝ) < Fintype.card γ := by exact_mod_cast Fintype.card_pos_iff.2 ⟨d⟩
  have hMG : ((univ.filter T).card : ℝ) ≤ Fintype.card γ := by
    exact_mod_cast card_le_univ _
  have hp0 : 0 ≤ uprob (fun ω => S ω = none) := uprob_nonneg _
  have hq : uprob (fun ω => S ω = some d) =
      (1 - uprob (fun ω => S ω = none)) / Fintype.card γ := by
    rw [eq_div_iff hG.ne']
    linarith
  rw [hq]
  have hrw : (1 - uprob (fun ω => S ω = none)) / Fintype.card γ * ((univ.filter T).card : ℝ) =
      (1 - uprob (fun ω => S ω = none)) * (((univ.filter T).card : ℝ) / Fintype.card γ) := by
    ring
  rw [hrw]
  have hr0 : (0 : ℝ) ≤ ((univ.filter T).card : ℝ) / Fintype.card γ :=
    div_nonneg (Nat.cast_nonneg _) hG.le
  have hr1 : ((univ.filter T).card : ℝ) / Fintype.card γ ≤ 1 := (div_le_one hG).2 hMG
  generalize ((univ.filter T).card : ℝ) / Fintype.card γ = r at hr0 hr1 ⊢
  generalize uprob (fun ω => S ω = none) = p at hp0 hf ⊢
  by_cases hTd : T d
  · rw [if_pos hTd]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩
  · rw [if_neg hTd]
    exact abs_le.2 ⟨by nlinarith, by nlinarith⟩

end TCSlib.Cryptography
