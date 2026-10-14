/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Foundations.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Computational indistinguishability: the sunglass and multicopy lemmas

The concrete layer of [Gar26, §3.2]. Distributions are samplers `X : σ → γ` from uniform
seeds, distinguishers are functions `D : γ → ρ → Bool` of a sample and uniform coins, and
`distAdv X Y D` is the advantage `|Pr[D(X) = 1] - Pr[D(Y) = 1]|`. Each lemma of the source
is stated as an explicit reduction: from a distinguisher `D` for the derived pair we build a
distinguisher for `X` and `Y` and prove an exact relation between the advantages. The
asymptotic statements ("if `X ≈ Y` then ...") follow once the reductions are shown to be
efficient, which is the job of the asymptotic layer.

Besides the two lemmas, the file provides the reseeding toolkit used by all reductions in
the pseudorandomness development: invariance of acceptance probabilities under bijections
of the seed space, under unused seed coordinates, and under moving a reduction's private
coins into the sampler; plus the *index-mixing* distinguisher that picks a hybrid index
uniformly at random, which turns the hybrid argument into a uniform reduction.

## Main definitions

* `pushSampler P X`: the sampler of `P(X)` for a randomized post-processing map `P`.
* `sunglassRed P D`: the distinguisher `D ∘ P` for `X` and `Y`.
* `mixDist D`: run `D k` for a uniformly random index `k`.
* `copies t X`: `t` independent copies of `X`.
* `multicopyHybrid X Y t k`: the hybrid `(Y, …, Y, X, …, X)` with `k` copies of `Y`.
* `multicopyRed X Y t k D`: the hybrid-`k` distinguisher for one copy.
* `multicopyAvgRed X Y t D`: the same with a uniformly random `k`.

## Main results

* `uprob_eq_of_equiv`, `acceptProb_comp_equiv`, `acceptProb_fst`, `acceptProb_snd`,
  `acceptProb_bind`, `acceptProb_update`: reseeding.
* `distAdv_mixDist_eq`: the averaged hybrid argument.
* `distAdv_sunglassRed`: [Gar26, Lemma 3.2], with equal advantage.
* `exists_multicopyRed_ge`: [Gar26, Lemma 3.3], some `k` has advantage `≥ ε / t`.
* `distAdv_multicopyAvgRed`: the averaged reduction has advantage exactly `ε / t`.

## References

* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §3.2 (Definition 3.4, Lemmas 3.2 and 3.3).
-/

namespace TCSlib.Cryptography

open Finset

variable {σ τ κ ρ ι γ δ : Type*} [Fintype σ] [Fintype τ] [Fintype κ] [Fintype ρ]

/-! ### Reseeding -/

/-- Two events that correspond under a bijection of the sample spaces have the same
probability: if `p a` holds exactly when `q (e a)` does, then `Pr[p] = Pr[q]`. -/
theorem uprob_eq_of_equiv {α β : Type*} [Fintype α] [Fintype β] (e : α ≃ β)
    {p : α → Prop} {q : β → Prop} (h : ∀ a, p a ↔ q (e a)) : uprob p = uprob q := by
  rw [← uprob_comp_equiv e q]
  congr 1
  funext a
  exact propext (h a)

/-- Relabelling the seed space of a sampler by a bijection does not change the probability
that a distinguisher accepts: a bijective image of a uniform seed is uniform. -/
theorem acceptProb_comp_equiv (e : σ ≃ τ) (X : τ → γ) (D : γ → ρ → Bool) :
    acceptProb (fun s => X (e s)) D = acceptProb X D :=
  uprob_eq_of_equiv (e.prodCongr (Equiv.refl ρ)) fun _ => Iff.rfl

/-- A seed coordinate that the sampler ignores does not change acceptance probabilities:
sampling `X` from the first coordinate of a uniform pair is sampling `X`. -/
theorem acceptProb_fst [Nonempty τ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb (fun z : σ × τ => X z.1) D = acceptProb X D := by
  let e : (σ × τ) × ρ ≃ (σ × ρ) × τ :=
    { toFun := fun w => ((w.1.1, w.2), w.1.2), invFun := fun z => ((z.1.1, z.2), z.1.2),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  unfold acceptProb
  exact (uprob_eq_of_equiv e (q := fun w : (σ × ρ) × τ => D (X w.1.1) w.1.2 = true)
    fun _ => Iff.rfl).trans (uprob_fst (fun y : σ × ρ => D (X y.1) y.2 = true))

/-- As `acceptProb_fst`, for an ignored first seed coordinate. -/
theorem acceptProb_snd [Nonempty τ] (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb (fun z : τ × σ => X z.2) D = acceptProb X D :=
  (acceptProb_comp_equiv (Equiv.prodComm τ σ) (fun z : σ × τ => X z.1) D).trans
    (acceptProb_fst X D)

/-- Moving coins into the sampler: a distinguisher that first draws private coins `c` and
feeds `P z c` to `D` accepts a sample of `X` with the probability that `D` accepts a sample
of the composite sampler `(s, c) ↦ P (X s) c`. -/
theorem acceptProb_bind (X : σ → γ) (P : γ → κ → δ) (D : δ → ρ → Bool) :
    acceptProb X (fun z (c : κ × ρ) => D (P z c.1) c.2) =
      acceptProb (fun s : σ × κ => P (X s.1) s.2) D :=
  uprob_eq_of_equiv (Equiv.prodAssoc σ κ ρ).symm fun _ => Iff.rfl

/-- Overwriting one coordinate of a uniform tuple with an independent uniform value leaves
the tuple uniform: a sampler fed `update u k x` for uniform `x` and `u` accepts with the
same probability as one fed `u`.

**Proof sketch.** The map `(x, u) ↦ (update u k x, u k)` is a bijection, and the sampler
ignores the second component of its image. -/
theorem acceptProb_update [DecidableEq ι] [Fintype ι] [Nonempty σ] (k : ι)
    (Z : (ι → σ) → τ → γ) (D : γ → ρ → Bool) :
    acceptProb (fun w : σ × ((ι → σ) × τ) => Z (Function.update w.2.1 k w.1) w.2.2) D =
      acceptProb (fun v : (ι → σ) × τ => Z v.1 v.2) D := by
  let e : σ × ((ι → σ) × τ) ≃ ((ι → σ) × τ) × σ :=
    { toFun := fun w => ((Function.update w.2.1 k w.1, w.2.2), w.2.1 k)
      invFun := fun v => (v.1.1 k, (Function.update v.1.1 k v.2, v.1.2))
      left_inv := fun w => by ext <;> simp
      right_inv := fun v => by ext <;> simp }
  rw [← acceptProb_fst (τ := σ) (fun v : (ι → σ) × τ => Z v.1 v.2) D]
  exact acceptProb_comp_equiv e (fun w : ((ι → σ) × τ) × σ => Z w.1.1 w.1.2) D

/-! ### The sunglass lemma -/

/-- The sampler of the post-processed distribution `P(X)`: draw a seed `s` of `X` and coins
`c` of `P`, output `P (X s) c`. -/
def pushSampler (P : γ → κ → δ) (X : σ → γ) : σ × κ → δ :=
  fun s => P (X s.1) s.2

/-- The sunglass reduction [Gar26, proof of Lemma 3.2]: from a distinguisher `D` of
`P(X)` and `P(Y)`, the distinguisher `D ∘ P` of `X` and `Y`. On input `z` it draws coins
for `P`, runs `P` once on `z`, and calls `D` once on the result with `D`'s own coins. -/
def sunglassRed (P : γ → κ → δ) (D : δ → ρ → Bool) : γ → κ × ρ → Bool :=
  fun z c => D (P z c.1) c.2

/-- The sunglass lemma, concrete form [Gar26, Lemma 3.2]: the distinguisher `D ∘ P` has
exactly the advantage between `X` and `Y` that `D` has between `P(X)` and `P(Y)`. The
post-processing `P` may be randomized, with coins from `κ`. -/
theorem distAdv_sunglassRed (P : γ → κ → δ) (X : σ → γ) (Y : τ → γ)
    (D : δ → ρ → Bool) :
    distAdv X Y (sunglassRed P D) = distAdv (pushSampler P X) (pushSampler P Y) D := by
  unfold distAdv sunglassRed pushSampler
  rw [acceptProb_bind, acceptProb_bind]

/-- The sunglass lemma for a deterministic post-processing map `P`: the distinguisher
`D ∘ P` has the advantage between `X` and `Y` that `D` has between `P ∘ X` and `P ∘ Y`.
[Gar26, Lemma 3.2]. -/
theorem distAdv_comp (P : γ → δ) (X : σ → γ) (Y : τ → γ) (D : δ → ρ → Bool) :
    distAdv X Y (fun z r => D (P z) r) = distAdv (fun s => P (X s)) (fun s => P (Y s)) D :=
  rfl

/-! ### Mixing over an index -/

/-- The distinguisher that draws an index `k` uniformly at random and runs `D k`. In a
hybrid argument this is the uniform reduction: it does not need to know the good hybrid
index. -/
def mixDist (D : ι → γ → ρ → Bool) : γ → ι × ρ → Bool :=
  fun z c => D c.1 z c.2

/-- The acceptance probability of the mixed distinguisher is the average over `k` of the
acceptance probabilities of the `D k`. -/
theorem acceptProb_mixDist [Fintype ι] (X : σ → γ) (D : ι → γ → ρ → Bool) :
    acceptProb X (mixDist D) = uexp fun k => acceptProb X (D k) := by
  let e : σ × (ι × ρ) ≃ ι × (σ × ρ) :=
    { toFun := fun w => (w.2.1, (w.1, w.2.2)), invFun := fun v => (v.2.1, (v.1, v.2.2)),
      left_inv := fun _ => rfl, right_inv := fun _ => rfl }
  unfold acceptProb mixDist
  exact (uprob_eq_of_equiv e (q := fun w : ι × (σ × ρ) => D w.1 (X w.2.1) w.2.2 = true)
    fun _ => Iff.rfl).trans (uprob_prod _)

/-- The averaged hybrid argument: if `D k` accepts `X` with probability `P k` and `Y` with
probability `P (k + 1)` for each `k < t`, then the mixed distinguisher has advantage exactly
`|P 0 - P t| / t`. [Gar26, proof of Lemma 3.3], uniform version.

**Proof sketch.** The difference of the averages is the average of the differences, which
telescopes to `(P 0 - P t) / t`. -/
theorem distAdv_mixDist_eq {t : ℕ} (X : σ → γ) (Y : τ → γ) (D : Fin t → γ → ρ → Bool)
    (P : ℕ → ℝ) (hX : ∀ k : Fin t, acceptProb X (D k) = P k)
    (hY : ∀ k : Fin t, acceptProb Y (D k) = P (k + 1)) :
    distAdv X Y (mixDist D) = |P 0 - P t| / t := by
  unfold distAdv
  rw [acceptProb_mixDist, acceptProb_mixDist]
  simp only [hX, hY, uexp, Fintype.card_fin]
  rw [← sub_div, ← Finset.sum_sub_distrib,
    Fin.sum_univ_eq_sum_range (fun i => P i - P (i + 1)), Finset.sum_range_sub', abs_div,
    Nat.abs_cast]

/-! ### The multicopy lemma -/

/-- The `t`-product of a sampler: `t` independent copies of `X`, sampled from `t`
independent seeds. [Gar26, Lemma 3.3]. -/
def copies (t : ℕ) (X : σ → γ) : (Fin t → σ) → Fin t → γ :=
  fun s i => X (s i)

/-- The `k`-th hybrid of the multicopy lemma: the first `k` coordinates are copies of `Y`,
the remaining `t - k` copies of `X`, all independent. [Gar26, proof of Lemma 3.3], the
hybrid `H_n^{(k,t)} = (Y^{(1)}, …, Y^{(k)}, X^{(k+1)}, …, X^{(t)})`. -/
def multicopyHybrid (X : σ → γ) (Y : τ → γ) (t k : ℕ) :
    (Fin t → σ) × (Fin t → τ) → Fin t → γ :=
  fun s i => if (i : ℕ) < k then Y (s.2 i) else X (s.1 i)

/-- The multicopy reduction at hybrid index `k` [Gar26, proof of Lemma 3.3]: on input `z`,
sample `k` copies of `Y` and `t - k - 1` copies of `X`, place `z` at position `k`
(0-indexed), and call `D` once on the resulting tuple. It uses `t - 1` calls to the
samplers of `X` and `Y` (it draws seeds for all `t` positions and ignores two of them);
this is where efficient samplability of `X` and `Y` is used.

Deviation: [Gar26] writes `B(Z) = A(X_1, …, X_{k-1}, Z, Y_{k+1}, …, Y_t)`, with copies of
`X` before `Z` and copies of `Y` after; that does not match its own hybrids, which put the
copies of `Y` first. Here the order matches the hybrids. -/
def multicopyRed (X : σ → γ) (Y : τ → γ) (t k : ℕ) (D : (Fin t → γ) → ρ → Bool) :
    γ → ((Fin t → σ) × (Fin t → τ)) × ρ → Bool :=
  fun z c => D (fun i => if (i : ℕ) < k then Y (c.1.2 i) else if (i : ℕ) = k then z
    else X (c.1.1 i)) c.2

/-- The zeroth hybrid is the `t`-product of `X`. -/
theorem acceptProb_multicopyHybrid_zero [Nonempty τ] (X : σ → γ) (Y : τ → γ) (t : ℕ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (multicopyHybrid X Y t 0) D = acceptProb (copies t X) D := by
  have h : multicopyHybrid X Y t 0 = fun s => copies t X s.1 := by
    funext s i
    simp [multicopyHybrid, copies]
  rw [h, acceptProb_fst]

/-- The `t`-th hybrid is the `t`-product of `Y`. -/
theorem acceptProb_multicopyHybrid_self [Nonempty σ] (X : σ → γ) (Y : τ → γ) (t : ℕ)
    (D : (Fin t → γ) → ρ → Bool) :
    acceptProb (multicopyHybrid X Y t t) D = acceptProb (copies t Y) D := by
  have h : multicopyHybrid X Y t t = fun s => copies t Y s.2 := by
    funext s i
    simp [multicopyHybrid, copies]
  rw [h, acceptProb_snd]

/-- On a sample of `X`, the hybrid-`k` reduction simulates the `k`-th hybrid for `D`.

**Proof sketch.** Its input is placed at position `k`, which in the `k`-th hybrid holds a
copy of `X`; overwriting the ignored seed at position `k` with the input's seed leaves the
seed tuple uniform. -/
theorem acceptProb_multicopyRed_left [Nonempty σ] (X : σ → γ) (Y : τ → γ) {t k : ℕ}
    (hk : k < t) (D : (Fin t → γ) → ρ → Bool) :
    acceptProb X (multicopyRed X Y t k D) = acceptProb (multicopyHybrid X Y t k) D := by
  refine (acceptProb_bind X (fun z (s : (Fin t → σ) × (Fin t → τ)) (i : Fin t) =>
    if (i : ℕ) < k then Y (s.2 i) else if (i : ℕ) = k then z else X (s.1 i)) D).trans ?_
  refine Eq.trans ?_ (acceptProb_update (ρ := ρ) (⟨k, hk⟩ : Fin t)
    (fun u (s' : Fin t → τ) => multicopyHybrid X Y t k (u, s')) D)
  congr 1
  funext w i
  simp only [multicopyHybrid, Function.update_apply, Fin.ext_iff]
  rcases lt_trichotomy (i : ℕ) k with h | h | h
  · simp [h]
  · simp [h]
  · simp [h.ne', not_lt.mpr h.le]

/-- On a sample of `Y`, the hybrid-`k` reduction simulates the `(k + 1)`-th hybrid for `D`.

**Proof sketch.** As in `acceptProb_multicopyRed_left`: position `k` holds a copy of `Y` in
the `(k + 1)`-th hybrid. -/
theorem acceptProb_multicopyRed_right [Nonempty τ] (X : σ → γ) (Y : τ → γ) {t k : ℕ}
    (hk : k < t) (D : (Fin t → γ) → ρ → Bool) :
    acceptProb Y (multicopyRed X Y t k D) = acceptProb (multicopyHybrid X Y t (k + 1)) D := by
  let e : τ × ((Fin t → σ) × (Fin t → τ)) ≃ τ × ((Fin t → τ) × (Fin t → σ)) :=
    (Equiv.refl τ).prodCongr (Equiv.prodComm _ _)
  refine (acceptProb_bind Y (fun z (s : (Fin t → σ) × (Fin t → τ)) (i : Fin t) =>
    if (i : ℕ) < k then Y (s.2 i) else if (i : ℕ) = k then z else X (s.1 i)) D).trans ?_
  refine Eq.trans ?_ ((acceptProb_comp_equiv e _ D).trans
    ((acceptProb_update (ρ := ρ) (⟨k, hk⟩ : Fin t)
      (fun u (s : Fin t → σ) => multicopyHybrid X Y t (k + 1) (s, u)) D).trans
    (acceptProb_comp_equiv (Equiv.prodComm _ _) (multicopyHybrid X Y t (k + 1)) D)))
  congr 1
  funext w i
  simp only [e, multicopyHybrid, Function.update_apply, Fin.ext_iff, Equiv.prodCongr_apply,
    Equiv.coe_refl, Equiv.prodComm_apply, Prod.map, Prod.fst_swap, Prod.snd_swap, id]
  rcases lt_trichotomy (i : ℕ) k with h | h | h
  · simp [h, Nat.lt_succ_of_lt h, h.ne]
  · simp [h]
  · simp [h.ne', not_lt.mpr h.le, not_lt.mpr (Nat.succ_le_of_lt h)]

/-- The multicopy lemma, concrete form [Gar26, Lemma 3.3]: if `D` distinguishes `t ≥ 1`
independent copies of `X` from `t` independent copies of `Y` with advantage `ε`, then for
some hybrid index `k < t` the reduction `multicopyRed X Y t k D` distinguishes one copy with
advantage at least `ε / t`. The index `k` is the non-uniform choice of the source
(footnote 2); `distAdv_multicopyAvgRed` removes it.

**Proof sketch.** The reduction at `k` accepts `X` and `Y` with the acceptance
probabilities of hybrids `k` and `k + 1`; the end hybrids are the two `t`-products, and
some neighbouring pair of hybrids is `ε / t` apart. -/
theorem exists_multicopyRed_ge [Nonempty σ] [Nonempty τ] (X : σ → γ) (Y : τ → γ) {t : ℕ}
    (ht : 0 < t) (D : (Fin t → γ) → ρ → Bool) :
    ∃ k < t, distAdv (copies t X) (copies t Y) D / t ≤ distAdv X Y (multicopyRed X Y t k D) := by
  obtain ⟨k, hk, hgap⟩ :=
    exists_hybrid_gap (fun i => acceptProb (multicopyHybrid X Y t i) D) ht
  refine ⟨k, hk, ?_⟩
  unfold distAdv
  rw [acceptProb_multicopyRed_left X Y hk, acceptProb_multicopyRed_right X Y hk,
    ← acceptProb_multicopyHybrid_zero X Y, ← acceptProb_multicopyHybrid_self X Y]
  exact hgap

/-- The uniform multicopy reduction: draw the hybrid index `k < t` uniformly at random and
run `multicopyRed X Y t k D`. It calls `D` once and the samplers `t - 1` times. -/
def multicopyAvgRed (X : σ → γ) (Y : τ → γ) (t : ℕ) (D : (Fin t → γ) → ρ → Bool) :
    γ → Fin t × (((Fin t → σ) × (Fin t → τ)) × ρ) → Bool :=
  mixDist fun k : Fin t => multicopyRed X Y t k D

/-- The multicopy lemma with a uniform reduction: the reduction with a random hybrid index
has advantage exactly `ε / t`, where `ε` is the advantage of `D` on the `t`-products.
[Gar26, Lemma 3.3].

**Proof sketch.** Average the identities of `acceptProb_multicopyRed_left` and
`acceptProb_multicopyRed_right` over `k`; the differences telescope. -/
theorem distAdv_multicopyAvgRed [Nonempty σ] [Nonempty τ] (X : σ → γ) (Y : τ → γ) (t : ℕ)
    (D : (Fin t → γ) → ρ → Bool) :
    distAdv X Y (multicopyAvgRed X Y t D) = distAdv (copies t X) (copies t Y) D / t := by
  rw [multicopyAvgRed, distAdv_mixDist_eq X Y _ (fun i => acceptProb (multicopyHybrid X Y t i) D)
    (fun k => acceptProb_multicopyRed_left X Y k.isLt D)
    (fun k => acceptProb_multicopyRed_right X Y k.isLt D), distAdv,
    acceptProb_multicopyHybrid_zero, acceptProb_multicopyHybrid_self]

end TCSlib.Cryptography
