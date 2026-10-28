/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.Proofs
import TCSlib.Cryptography.ZeroKnowledge.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The graph protocols: shadow copies of the concrete repetition lemmas

Shadow copies (namespace `TCSlib.Cryptography.GI`, for the proofs of the `|x|`-fold protocols
in `GraphIsomorphism/SoundnessRep.lean`) of the concrete probability lemmas of the main file
`ZeroKnowledge/GraphIsomorphism.lean` that are stated with the main file's definitions
`prefixLT`, `prefixLE` and `Isomorphic`: the adaptive guessing lemma (Lem-119.c), the `n`-fold
soundness of the graph non-isomorphism protocol against adaptive provers (Lem-119.b), the
`m`-fold soundness of the graph isomorphism protocol (Lem-120.d), and the negligibility of the
sampling term (Inf-4.4). The statements and proofs are those of the main file verbatim (with
`GI.prefixLT`, `GI.prefixLE`, `GI.Isomorphic`, `GI.permFailBound`, `GI.instanceVertices`, all
definitionally equal to the originals); the main file cannot be imported here, and its
proofs cannot be moved out without moving the public statements.

## Main definitions

* `TCSlib.Cryptography.GI.prefixLT`, `GI.prefixLE` — shadows of the prefix maps of a bit tuple.

## Main results

* `TCSlib.Cryptography.GI.uprob_adaptive_guess` — the adaptive guessing lemma `2^{-m}`
  (Lem-119.c).
* `TCSlib.Cryptography.GI.uprob_gi_rep_cheat_le` — `m`-fold GI soundness (Lem-120.d).
* `TCSlib.Cryptography.GI.uprob_gni_rep_cheat` — `n`-fold GNI soundness (Lem-119.b).
* `TCSlib.Cryptography.GI.negligible_mul_permFailBound` — the sampling term is negligible.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.5 Interactive proofs, pp. 117–120.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026 (the concrete probability layer).
-/

namespace TCSlib.Cryptography.GI

open Complexity Turing Finset

/-- The sampling error of the repeated protocols, `|x| · permFailBound n` with
`n = instanceVertices |x|`, is negligible in `|x|` (Inf-4.4): for `N ≥ 8`,
`√(N/4) ≤ instanceVertices N ≤ N`, so the term is at most `N² · 2^{-√(N/4)}`
(`negligible_two_pow_neg_sqrt_div`, `Negligible.mul_pow`, `Negligible.mono`).

**Repair (run-3 audit P2-1):** proved (the run-2 sketch went through `permFailBound_le_exp`,
removed). -/
theorem negligible_mul_permFailBound :
    Negligible fun N : ℕ => (N : ℝ) * permFailBound (instanceVertices N) := by
  refine ((negligible_two_pow_neg_sqrt_div (C := 4) (by norm_num)).mul_pow 2).mono
    ⟨8, fun N hN => ?_⟩
  have hv : instanceVertices N ≤ N := (Nat.sqrt_le_self _).trans (by omega)
  have hsq : Nat.sqrt (N / 4) ≤ instanceVertices N := Nat.sqrt_le_sqrt (by omega)
  have hpow : (2 : ℝ)⁻¹ ^ instanceVertices N ≤ (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) :=
    pow_le_pow_of_le_one (by norm_num) (by norm_num) hsq
  have hv' : (instanceVertices N : ℝ) ≤ N := by exact_mod_cast hv
  unfold permFailBound
  rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
  calc (N : ℝ) * (instanceVertices N * (2 : ℝ)⁻¹ ^ instanceVertices N)
      ≤ N * (N * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4)) := by gcongr
    _ = (N : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ Nat.sqrt (N / 4) := by ring

/-- The strict prefix `b_0, …, b_{i-1}` of a bit tuple (the history an adaptive prover has
seen before challenge `i`). -/
def prefixLT {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin i → α :=
  fun j => b (Fin.castLE i.isLt.le j)

/-- The prefix `b_0, …, b_i` of a tuple (the history including the current challenge). -/
def prefixLE {m : ℕ} {α : Type*} (b : Fin m → α) (i : Fin m) : Fin (i + 1) → α :=
  fun j => b (Fin.castLE i.isLt j)

/-- The adaptive guess map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` of Lem-119.c: triangular with
identity diagonal, hence a bijection of `Fin m → Bool` for every `w` (`adaptiveXorEquiv`); it
carries the event "`b_i = g_i(b_{<i}, w)` for every `i`" to "`b = 0`". -/
private def adaptiveXor {m : ℕ} {W : Type*} (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W)
    (b : Fin m → Bool) : Fin m → Bool :=
  fun i => xor (b i) (g i (prefixLT b i) w)

/-- `adaptiveXor g w` is injective.

**Proof sketch.** If the images agree then `b_i = b'_i` for every `i`, by induction on a bound
`k > i`: the prefixes `b_{<i}`, `b'_{<i}` agree by the induction hypothesis, so the guesses
`g_i(b_{<i}, w)`, `g_i(b'_{<i}, w)` agree and `xor` cancels (`Bool.xor_left_inj`). -/
private theorem adaptiveXor_injective {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) :
    Function.Injective (adaptiveXor g w) := by
  intro b b' h
  have key : ∀ k, ∀ i : Fin m, i.val < k → b i = b' i := by
    intro k
    induction k with
    | zero => intro i hi; exact absurd hi (Nat.not_lt_zero _)
    | succ k ih =>
      intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hlt | heq
      · exact ih i hlt
      · have hpre : prefixLT b i = prefixLT b' i := by
          funext j
          have hj := j.isLt
          exact ih _ (by simp only [Fin.coe_castLE]; omega)
        have hi' := congrFun h i
        simp only [adaptiveXor, hpre] at hi'
        exact Bool.xor_left_inj.mp hi'
  funext i
  exact key (i.val + 1) i (Nat.lt_succ_self _)

/-- The bijection `adaptiveXor g w` of `Fin m → Bool` (an injection of a finite type into
itself, `Finite.injective_iff_bijective`). -/
private noncomputable def adaptiveXorEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) (w : W) : (Fin m → Bool) ≃ (Fin m → Bool) :=
  Equiv.ofBijective (adaptiveXor g w)
    (Finite.injective_iff_bijective.mp (adaptiveXor_injective g w))

/-- The coin bijection `(b, w) ↦ (adaptiveXor g w b, w)` of `(Fin m → Bool) × W`. -/
private noncomputable def adaptiveEquiv {m : ℕ} {W : Type*}
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) : (Fin m → Bool) × W ≃ (Fin m → Bool) × W where
  toFun z := (adaptiveXorEquiv g z.2 z.1, z.2)
  invFun z := ((adaptiveXorEquiv g z.2).symm z.1, z.2)
  left_inv z := by simp
  right_inv z := by simp

/-- The adaptive guessing lemma [PS10, proof of Proposition 118.4, "each iteration is
independent of all prior iterations"] (Lem-119.c): for every finite nonempty `W` and every
family of guesses `g i` depending on the earlier bits and on `w`, the probability that a
uniform tuple `b` satisfies `b_i = g_i(b_{<i}, w)` for every `i` is exactly `2^{-m}`. The
engine of every `2^{-n}` soundness bound against adaptive provers.

**Deviation:** `W` nonempty (`uprob` on an empty type is `0`, so the equality fails for
`W = Empty`; every consumer uses a tape type `Fin k → Bool`).

**Repair (run-3 audit P10-1):** hypothesis `[Nonempty W]` added (the run-2 statement
specialised to `W := Empty`, `m := 0` reads `0 = 1`).

**Proof sketch.** For each `w` the map `b ↦ (i ↦ b_i xor g_i(b_{<i}, w))` is a bijection of
`Fin m → Bool` (`adaptiveXorEquiv`: triangular with identity diagonal, injective by strong
induction on `i`, hence bijective on a finite type) carrying the event to `{b = 0}`; so
`uprob_comp_equiv` with the coin bijection `adaptiveEquiv`, `uprob_fst` (here `W ≠ ∅` is
used) and `OneWay.uprob_eq_one_div_card` give `1 / 2^m` (`Fintype.card_fun`). Equivalently,
exactly one `b` per `w` satisfies all the constraints (`|W|` elements out of `2^m |W|`). -/
theorem uprob_adaptive_guess (m : ℕ) {W : Type*} [Fintype W] [Nonempty W]
    (g : (i : Fin m) → (Fin i → Bool) → W → Bool) :
    uprob (fun z : (Fin m → Bool) × W => ∀ i, z.1 i = g i (prefixLT z.1 i) z.2) =
      (2 : ℝ)⁻¹ ^ m := by
  have hev : ∀ z : (Fin m → Bool) × W,
      (∀ i, z.1 i = g i (prefixLT z.1 i) z.2) ↔ (adaptiveEquiv g z).1 = fun _ => false := by
    intro z
    simp only [adaptiveEquiv, adaptiveXorEquiv, Equiv.coe_fn_mk, Equiv.ofBijective_apply,
      adaptiveXor, funext_iff]
    exact forall_congr' fun i => by cases z.1 i <;> cases g i (prefixLT z.1 i) z.2 <;> simp
  rw [OneWay.uprob_congr hev,
    uprob_comp_equiv (adaptiveEquiv g) (fun z : (Fin m → Bool) × W => z.1 = fun _ => false),
    uprob_fst (β := W) (fun b : Fin m → Bool => b = fun _ => false),
    OneWay.uprob_eq_one_div_card (fun _ : Fin m => false), Fintype.card_fun, Fintype.card_bool,
    Fintype.card_fin]
  push_cast
  rw [one_div, inv_pow]

/-- Soundness of the `m`-fold graph isomorphism protocol against adaptive provers
[PS10, Proposition 120.7, "repeated … to drive the error as low as desired"] (Lem-120.d):
if `G₀ ≇ G₁` then for a prover whose `i`-th graph `H_i` depends on the earlier challenges and
its coins and whose `i`-th reply `γ_i` also depends on the current challenge, the verifier
accepts all `m` iterations with probability at most `2^{-m}`.

**Proof sketch.** For empty `ρ` the probability is `0`. Otherwise acceptance in iteration `i` forces
`b_i = g_i(b_{<i}, r)` for the guess `g_i := decide (G₁ ≅ H_i)` (`not_isomorphic_both`), so
`uprob_mono` reduces to `uprob_adaptive_guess`.

**Repair (run-3 audit P10-1):** statement unchanged (an inequality, true for empty coins);
the proof splits on `ρ` empty since `uprob_adaptive_guess` now assumes `Nonempty`. -/
theorem uprob_gi_rep_cheat_le {n m : ℕ} {ρ : Type*} [Fintype ρ] {G₀ G₁ : Graph n}
    (h : ¬ Isomorphic G₀ G₁) (H : (i : Fin m) → (Fin i → Bool) → ρ → Graph n)
    (γ : (i : Fin m) → (Fin (i + 1) → Bool) → ρ → Equiv.Perm (Fin n)) :
    uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
      permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) ≤
      (2 : ℝ)⁻¹ ^ m := by
  rcases isEmpty_or_nonempty ρ with hρ | hρ
  · have h0 : uprob (fun z : (Fin m → Bool) × ρ => ∀ i,
        permGraph (cond (z.1 i) G₁ G₀) (γ i (prefixLE z.1 i) z.2) = H i (prefixLT z.1 i) z.2) = 0 := by
      classical
      rw [uprob_eq_card_filter, Fintype.card_eq_zero]
      simp
    rw [h0]
    positivity
  · rw [← uprob_adaptive_guess m fun i p r => decide (Isomorphic G₁ (H i p r))]
    refine uprob_mono fun z hz i => ?_
    have hi := hz i
    cases hb : z.1 i
    · rw [hb] at hi
      have h0 : Isomorphic G₀ (H i (prefixLT z.1 i) z.2) := ⟨_, hi⟩
      exact (decide_eq_false fun h1 => not_isomorphic_both h ⟨h0, h1⟩).symm
    · rw [hb] at hi
      exact (decide_eq_true ⟨_, hi⟩).symm

/-- The change of variables of Lem-119.b, `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, with the
coins regrouped as `(b, (σ, w))` (inverse: multiply by `σ₀` instead). -/
private def gniShear {n m : ℕ} (ρ : Type*) (σ₀ : Equiv.Perm (Fin n)) :
    (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ) ≃
      ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ where
  toFun z := ((z.1, fun i => if z.1 i then z.2.1 i * σ₀⁻¹ else z.2.1 i), z.2.2)
  invFun z := (z.1.1, (fun i => if z.1.1 i then z.1.2 i * σ₀ else z.1.2 i, z.2))
  left_inv z := by
    rcases z with ⟨b, σ, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp
  right_inv z := by
    rcases z with ⟨⟨b, σ⟩, w⟩
    simp only [Prod.mk.injEq, true_and, and_true]
    funext i
    cases hb : b i <;> simp

/-- Under `gniShear` every graph `H_j = σ'_j(G₀)` is independent of `b`
(`permGraph_mul_inv_of_eq`), so the event "every reply equals the verifier's bit" is the
adaptive guessing event of `uprob_adaptive_guess` with guesses ignoring the earlier bits. -/
private theorem gniShear_event_iff {n m : ℕ} {ρ : Type*} {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    ∀ z : (Fin m → Bool) × ((Fin m → Equiv.Perm (Fin n)) × ρ),
      (∀ i, g i (prefixLE (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ z).1.1 j) G₁ G₀)
          ((gniShear (m := m) ρ σ₀ z).1.2 j)) i) (gniShear (m := m) ρ σ₀ z).2 =
            (gniShear (m := m) ρ σ₀ z).1.1 i) ↔
      (∀ i, z.1 i = g i (prefixLE (fun j => permGraph G₀ (z.2.1 j)) i) z.2.2) := by
  rintro ⟨b, σ, w⟩
  have hH : (fun j => permGraph (cond ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.1 j) G₁ G₀)
      ((gniShear (m := m) ρ σ₀ (b, σ, w)).1.2 j)) = fun j => permGraph G₀ (σ j) := by
    funext j
    show permGraph (cond (b j) G₁ G₀) (if b j then σ j * σ₀⁻¹ else σ j) = permGraph G₀ (σ j)
    cases b j
    · rfl
    · exact permGraph_mul_inv_of_eq hσ (σ j)
  rw [hH]
  exact forall_congr' fun i => eq_comm

/-- Soundness of the `m`-fold graph non-isomorphism protocol against adaptive provers
[PS10, proof of Proposition 118.4] (Lem-119.b): if `σ₀(G₀) = G₁`, then for every prover
whose `i`-th reply `g_i` depends on the graphs `H_0, …, H_i` received so far and on its
(nonempty type of) coins `w`, the probability (over the verifier's bits `b`, permutations `σ`
and `w`) that every reply equals the verifier's bit is exactly `2^{-m}`.

**Deviation:** `ρ` nonempty (`uprob` on an empty type is `0`; the consumer
`gni_interactiveProof` uses `ρ := P'.Coins |x|`, a tape type).

**Repair (run-3 audit P10-2):** hypothesis `[Nonempty ρ]` added (the run-2 statement
specialised to `ρ := Empty`, `n = m = 0`, `σ₀ = 1` reads `0 = 1`).

**Proof sketch.** Change variables `σ_i ↦ if b_i then σ_i σ₀⁻¹ else σ_i`, a bijection of the
coins fixing `b` and `w` (`gniShear`, with `uprob_comp_equiv`); then every `H_i = σ'_i(G₀)`
(`permGraph_mul_inv_of_eq`, `hσ`) is a function of `σ'` alone, the event is
`∀ i, b_i = g'_i(b_{<i}, (σ', w))` with `g'_i` ignoring `b_{<i}` (`gniShear_event_iff`), and
`uprob_adaptive_guess` with `W := (Fin m → S_n) × ρ` (nonempty since `ρ` is) gives
`2^{-m}`. -/
theorem uprob_gni_rep_cheat {n m : ℕ} {ρ : Type*} [Fintype ρ] [Nonempty ρ] {G₀ G₁ : Graph n}
    {σ₀ : Equiv.Perm (Fin n)} (hσ : permGraph G₀ σ₀ = G₁)
    (g : (i : Fin m) → (Fin (i + 1) → Graph n) → ρ → Bool) :
    uprob (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i) =
      (2 : ℝ)⁻¹ ^ m := by
  have h1 := uprob_comp_equiv (gniShear (m := m) ρ σ₀)
    (fun z : ((Fin m → Bool) × (Fin m → Equiv.Perm (Fin n))) × ρ => ∀ i,
      g i (prefixLE (fun j => permGraph (cond (z.1.1 j) G₁ G₀) (z.1.2 j)) i) z.2 = z.1.1 i)
  have h2 := uprob_adaptive_guess m
    fun i (_ : Fin i → Bool) (w : (Fin m → Equiv.Perm (Fin n)) × ρ) =>
      g i (prefixLE (fun j => permGraph G₀ (w.1 j)) i) w.2
  rw [← h1, ← h2]
  exact OneWay.uprob_congr (gniShear_event_iff hσ g)


end TCSlib.Cryptography.GI
