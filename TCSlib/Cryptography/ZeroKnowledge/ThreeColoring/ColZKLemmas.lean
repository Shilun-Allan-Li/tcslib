/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.SimulatorLemmas
import TCSlib.Cryptography.ZeroKnowledge.ThreeColoring.Machines
import TCSlib.Cryptography.ZeroKnowledge.CommitmentLemmas

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Generic lemmas for the zero-knowledge proof of graph 3-colouring

Generic facts used by the fill ladder of `col_zk` (`ThreeColoring/Simulator.lean`, the proof of
[PS10, Proposition 128.8]): reading disjoint fields of a uniform tape gives independent uniform
fields (`pushesUniform_restrict`, `pushesUniform_offsetTable`), and the bookkeeping of the error
function (`negligible_colZKErr`).

## Main definitions

* None: this file holds lemmas only.

## Main results

* `TCSlib.Cryptography.ColZK.pushesUniform_restrict` — restricting a uniform table along an
  injective map gives a uniform table.
* `TCSlib.Cryptography.ColZK.pushesUniform_offsetTable`, `pushesUniform_blockFields` — disjoint
  fields of a uniform tape are independent and uniform.
* `TCSlib.Cryptography.ColZK.exists_fixSeed`, `distAdv_seed_to_coins`,
  `acceptProb_comp_pushesUniform` — averaging over seeds.
* `TCSlib.Cryptography.ColZK.findSome?_finRange_split_lt` — a first-success search split at an
  index.
* `TCSlib.Cryptography.ColZK.negligible_colZKErr` — the error of `col_zk` is negligible.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§4.7: Proposition 128.8 and its proof, p. 129.)
-/

namespace TCSlib.Cryptography.ColZK

open Complexity Turing

/-! ### Uniform fields of a uniform tape -/

/-- **Restricting a uniform table along an injective map gives a uniform table**: for an
injective `r : J → I`, `R ↦ R ∘ r` pushes the uniform distribution on `I → O` to the uniform
distribution on `J → O`. Generic form (any finite `J`) of `pushesUniform_comp_injective` of
`Asymptotic/MultiMessage.lean` (stated there for `J = Fin (q + 1)`; that file is not upstream of
this one), with the same proof.

**Proof sketch.** Split `I` into the image of `r` and its complement (`Equiv.ofInjective`,
`Equiv.Set.sumCompl`): the table is the pair of its restrictions
(`Equiv.sumArrowEquivProdArrow`), and `R ∘ r` is the first one (`pushesUniform_fst`). -/
theorem pushesUniform_restrict {I J O : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype O] [Nonempty O] {r : J → I} (hr : Function.Injective r) :
    HardcoreBit.PushesUniform (fun R : I → O => fun j => R (r j)) := by
  classical
  let e₁ : J ⊕ ((Set.range r)ᶜ : Set I) ≃ I :=
    (Equiv.sumCongr (Equiv.ofInjective r hr) (Equiv.refl _)).trans
      (Equiv.Set.sumCompl (Set.range r))
  let e : (I → O) ≃ (J → O) × (((Set.range r)ᶜ : Set I) → O) :=
    (Equiv.arrowCongr e₁.symm (Equiv.refl O)).trans (Equiv.sumArrowEquivProdArrow _ _ _)
  have he : (fun R : I → O => fun j => R (r j)) = fun R => (e R).1 := by
    funext R j
    simp [e, e₁]
  rw [he]
  exact (HardcoreBit.pushesUniform_equiv e).comp HardcoreBit.pushesUniform_fst

/-- Entry `(i, j)` of an `n × k` table sits at position `i k + j < n k`. -/
theorem table_index_lt {n k : ℕ} (i : Fin n) (j : Fin k) : (i : ℕ) * k + j < n * k := by
  have h1 := i.isLt
  have h2 := j.isLt
  calc (i : ℕ) * k + j < (i : ℕ) * k + k := by omega
    _ = ((i : ℕ) + 1) * k := by ring
    _ ≤ n * k := Nat.mul_le_mul_right _ h1

/-- The table positions `i k + j` determine `(i, j)`. -/
theorem table_index_inj {n k : ℕ} {i i' : Fin n} {j j' : Fin k}
    (h : (i : ℕ) * k + j = (i' : ℕ) * k + j') : i = i' ∧ j = j' := by
  have hk : 0 < k := Nat.lt_of_le_of_lt (Nat.zero_le _) j.isLt
  have hd := congrArg (· / k) h
  have hm := congrArg (· % k) h
  simp only [Nat.mul_comm _ k, Nat.mul_add_div hk, Nat.div_eq_of_lt j.isLt,
    Nat.div_eq_of_lt j'.isLt, Nat.mul_add_mod, Nat.mod_eq_of_lt j.isLt,
    Nat.mod_eq_of_lt j'.isLt] at hd hm
  exact ⟨Fin.ext (by simpa using hd), Fin.ext hm⟩

/-- **A prefix and a table at an offset of a uniform tape are independent and uniform**: for
`a + n k ≤ L`, the map sending a tape `t` of `L` bits to its first `a` bits and to the
`n × k` table `(i, j) ↦ t (a + i k + j)` pushes uniform to uniform.

**Proof sketch.** The two fields read the tape along the injective map
`Fin a ⊕ (Fin n × Fin k) → Fin L`, `inl i ↦ i`, `inr (i, j) ↦ a + i k + j` (`table_index_inj`),
so `pushesUniform_restrict` applies; the pair of fields is that restriction followed by the
bijection `Equiv.sumArrowEquivProdArrow` and `Equiv.curry`. -/
theorem pushesUniform_offsetTable {L a n k : ℕ} (h : a + n * k ≤ L) :
    HardcoreBit.PushesUniform (fun t : Fin L → Bool =>
      ((fun i : Fin a => t (Fin.castLE (by omega) i)),
        fun (i : Fin n) (j : Fin k) => t ⟨a + (i * k + j), by
          have := table_index_lt i j
          omega⟩)) := by
  let r : Fin a ⊕ (Fin n × Fin k) → Fin L := Sum.elim (fun i => Fin.castLE (by omega) i)
    fun p => ⟨a + (p.1 * k + p.2), by have := table_index_lt p.1 p.2; omega⟩
  have hr : Function.Injective r := by
    rintro (i | ⟨i, j⟩) (i' | ⟨i', j'⟩) hij <;> simp only [r, Sum.elim_inl, Sum.elim_inr,
      Fin.ext_iff, Fin.coe_castLE] at hij
    · rw [Fin.ext hij]
    · have := i.isLt
      omega
    · have := i'.isLt
      omega
    · obtain ⟨rfl, rfl⟩ := table_index_inj (by omega : (i : ℕ) * k + j = (i' : ℕ) * k + j')
      rfl
  let e : (Fin a ⊕ (Fin n × Fin k) → Bool) ≃ (Fin a → Bool) × (Fin n → Fin k → Bool) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans
      (Equiv.prodCongr (Equiv.refl _) (Equiv.curry _ _ _))
  exact (pushesUniform_restrict (O := Bool) hr).comp (HardcoreBit.pushesUniform_equiv e)

/-- **Four disjoint fields of a uniform tape are independent and uniform**: for offsets
`a₁ ≤ o₂`, `o₂ + a₂ ≤ o₃`, `o₃ + n k ≤ o₄`, `o₄ + a₄ ≤ L`, the map sending a tape `t` of `L`
bits to its first `a₁` bits, its `a₂` bits from `o₂`, the `n × k` table `(i, j) ↦ t (o₃ + i k + j)`
and its `a₄` bits from `o₄` pushes uniform to uniform (the layout of one coin block of the
simulator, `colSimBlock`).

**Proof sketch.** The fields read the tape along an injective map
`((Fin a₁ ⊕ Fin a₂) ⊕ (Fin n × Fin k)) ⊕ Fin a₄ → Fin L` (disjoint ranges, `table_index_inj`), so
`pushesUniform_restrict` applies, followed by the bijection `Equiv.sumArrowEquivProdArrow` (three
times) and `Equiv.curry`. -/
theorem pushesUniform_blockFields {L a₁ o₂ a₂ o₃ n k o₄ a₄ : ℕ} (h₁ : a₁ ≤ o₂)
    (h₂ : o₂ + a₂ ≤ o₃) (h₃ : o₃ + n * k ≤ o₄) (h₄ : o₄ + a₄ ≤ L) :
    HardcoreBit.PushesUniform (fun t : Fin L → Bool =>
      ((((fun i : Fin a₁ => t ⟨i, by have := i.isLt; omega⟩),
        fun i : Fin a₂ => t ⟨o₂ + i, by have := i.isLt; omega⟩),
        fun (i : Fin n) (j : Fin k) => t ⟨o₃ + (i * k + j), by
          have := table_index_lt i j
          omega⟩),
        fun i : Fin a₄ => t ⟨o₄ + i, by have := i.isLt; omega⟩)) := by
  let r : ((Fin a₁ ⊕ Fin a₂) ⊕ (Fin n × Fin k)) ⊕ Fin a₄ → Fin L :=
    Sum.elim (Sum.elim (Sum.elim (fun i => ⟨i, by have := i.isLt; omega⟩)
      fun i => ⟨o₂ + i, by have := i.isLt; omega⟩)
      fun p => ⟨o₃ + (p.1 * k + p.2), by have := table_index_lt p.1 p.2; omega⟩)
      fun i => ⟨o₄ + i, by have := i.isLt; omega⟩
  have hr : Function.Injective r := by
    rintro (((i | i) | ⟨i, j⟩) | i) (((i' | i') | ⟨i', j'⟩) | i') hij <;>
      simp only [r, Sum.elim_inl, Sum.elim_inr, Fin.ext_iff] at hij <;>
      first
        | (have := table_index_lt i j; have := table_index_lt i' j'; omega)
        | (have := table_index_lt i j; have := i'.isLt; omega)
        | (have := table_index_lt i' j'; have := i.isLt; omega)
        | (have := i.isLt; have := i'.isLt; first | (rw [Fin.ext (by omega : (i : ℕ) = i')]) | omega)
        | skip
    obtain ⟨rfl, rfl⟩ := table_index_inj (by omega : (i : ℕ) * k + j = (i' : ℕ) * k + j')
    rfl
  let e : (((Fin a₁ ⊕ Fin a₂) ⊕ (Fin n × Fin k)) ⊕ Fin a₄ → Bool) ≃
      (((Fin a₁ → Bool) × (Fin a₂ → Bool)) × (Fin n → Fin k → Bool)) × (Fin a₄ → Bool) :=
    (Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr
      ((Equiv.sumArrowEquivProdArrow _ _ _).trans (Equiv.prodCongr
        (Equiv.sumArrowEquivProdArrow _ _ _) (Equiv.curry _ _ _))) (Equiv.refl _))
  exact (pushesUniform_restrict (O := Bool) hr).comp (HardcoreBit.pushesUniform_equiv e)

/-! ### Averaging over seeds -/

/-- A sampler precomposed with a map pushing uniform to uniform has the same acceptance
probability (`PushesUniform.prodMap` with the identity on the coins, `acceptProb_def`). -/
theorem acceptProb_comp_pushesUniform {Ω σ γ ρ : Type*} [Fintype Ω] [Fintype σ] [Fintype ρ]
    {π : Ω → σ} (hπ : HardcoreBit.PushesUniform π) (X : σ → γ) (D : γ → ρ → Bool) :
    acceptProb (fun ω => X (π ω)) D = acceptProb X D := by
  rw [acceptProb_def, acceptProb_def]
  exact (hπ.prodMap HardcoreBit.pushesUniform_id).uprob_eq fun z : σ × ρ => D (X z.1) z.2 = true

/-- **Fixing a seed factor of the first sampler**: for `X` on seeds `κ × σ` some `k₀` has
`|Pr[D(X) = 1] − Pr[D(Y) = 1]| ≤ distAdv (X (k₀, ·)) Y D`.

**Proof sketch.** `Pr[D(X) = 1]` is the average over `k` of `Pr[D(X (k, ·)) = 1]`
(`acceptProb_def`, `Equiv.prodAssoc`, `uprob_prod`) and `Pr[D(Y) = 1]` the average of a constant
(`HardcoreBit.uexp_const`); some `k₀` has the absolute difference at least the average's
(`HardcoreBit.uexp_sub`, `CommitmentLemmas.exists_abs_uexp_le`). -/
theorem exists_fixSeed {κ σ τ γ ρ : Type*} [Fintype κ] [Nonempty κ] [Fintype σ] [Fintype τ]
    [Fintype ρ] (X : κ × σ → γ) (Y : τ → γ) (D : γ → ρ → Bool) :
    ∃ k₀ : κ, |acceptProb X D - acceptProb Y D| ≤ distAdv (fun s => X (k₀, s)) Y D := by
  have hX : acceptProb X D = uexp fun k => acceptProb (fun s => X (k, s)) D := by
    rw [acceptProb_def, ← uprob_comp_equiv (Equiv.prodAssoc κ σ ρ).symm, uprob_prod]
    simp only [acceptProb_def]
    rfl
  obtain ⟨k₀, hk₀⟩ := CommitmentLemmas.exists_abs_uexp_le fun k =>
    acceptProb (fun s => X (k, s)) D - acceptProb Y D
  refine ⟨k₀, ?_⟩
  rw [distAdv_def, hX, ← HardcoreBit.uexp_const (Ω := κ) (acceptProb Y D), ← HardcoreBit.uexp_sub,
    HardcoreBit.uexp_const]
  exact hk₀

/-- **Moving a seed factor into the distinguisher's coins**: post-processing two samplers by
`F · k` with an independent uniform `k` is post-processing by a distinguisher with coins
`κ × ρ` (`acceptProb_bind` on both samplers). -/
theorem distAdv_seed_to_coins {σ τ κ γ γ' ρ : Type*} [Fintype σ] [Fintype τ] [Fintype κ]
    [Fintype ρ] (X : σ → γ) (Y : τ → γ) (F : γ → κ → γ') (D : γ' → ρ → Bool) :
    distAdv (fun s : σ × κ => F (X s.1) s.2) (fun s : τ × κ => F (Y s.1) s.2) D =
      distAdv X Y fun g (c : κ × ρ) => D (F g c.1) c.2 := by
  rw [distAdv_def, distAdv_def, acceptProb_bind, acceptProb_bind]

/-- Every advantage is at most `1` (`distAdv_le_of_statClose`; probabilities lie in `[0, 1]`). -/
theorem distAdv_le_one {σ τ γ ρ : Type*} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ)
    (Y : τ → γ) (D : γ → ρ → Bool) : distAdv X Y D ≤ 1 :=
  distAdv_le_of_statClose X Y ((statClose_iff X Y 1).2 fun T => abs_sub_le_iff.2
    ⟨by linarith [uprob_le_one fun s => T (X s), uprob_nonneg fun t => T (Y t)],
      by linarith [uprob_le_one fun t => T (Y t), uprob_nonneg fun s => T (X s)]⟩) D

/-! ### Tapes as lists -/

/-- A window of a tape: `((List.ofFn b).drop a).take k` is the tape of the `k` bits from `a`. -/
theorem ofFn_drop_take {L : ℕ} (b : Fin L → Bool) (a k : ℕ) (h : a + k ≤ L) :
    ((List.ofFn b).drop a).take k = List.ofFn fun i : Fin k => b ⟨a + i, by have := i.isLt; omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  · intro i h₁ h₂
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- A suffix of a tape: `(List.ofFn b).drop a` is the tape of the last `k = L − a` bits. -/
theorem ofFn_drop_eq {L : ℕ} (b : Fin L → Bool) (a k : ℕ) (h : a + k = L) :
    (List.ofFn b).drop a = List.ofFn fun i : Fin k => b ⟨a + i, by have := i.isLt; omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_ofFn]
    omega
  · intro i h₁ h₂
    simp only [List.getElem_drop, List.getElem_ofFn]

/-- A window ending at `B ≤ L`: `((List.ofFn b).take B).drop a` is the tape of the `k = B − a`
bits from `a`. -/
theorem ofFn_take_drop {L : ℕ} (b : Fin L → Bool) (a k B : ℕ) (h : a + k = B) (hB : B ≤ L) :
    ((List.ofFn b).take B).drop a =
      List.ofFn fun i : Fin k => b ⟨a + i, by have := i.isLt; omega⟩ := by
  apply List.ext_getElem
  · simp only [List.length_drop, List.length_take, List.length_ofFn]
    omega
  · intro i h₁ h₂
    simp only [List.getElem_drop, List.getElem_take, List.getElem_ofFn]

/-! ### Searches -/

/-- Mapping the values of a search: `l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g`
(core `List.map_findSome?`, read from right to left, with the composite written pointwise). -/
theorem findSome?_map_option {α β γ : Type*} (l : List α) (f : α → Option β) (g : β → γ) :
    l.findSome? (fun a => (f a).map g) = (l.findSome? f).map g :=
  List.map_findSome?.symm

/-- A search over `List.range K` is the search over `List.finRange K` of the same values. -/
theorem findSome?_range_eq_finRange {β : Type*} (K : ℕ) (g : ℕ → Option β) :
    (List.range K).findSome? g = (List.finRange K).findSome? fun t : Fin K => g t := by
  rw [← List.map_coe_finRange, List.findSome?_map]
  rfl

/-! ### The error of `col_zk` -/

/-- **The error function of `col_zk` is negligible**: if `εB (√N)` is negligible in `N` then so
is `N² εB (√N) + e^{−√N} + N² ((1/2)^N + (1/4)^N) + (1/4)^N` (gate 03g review §2.3).

**Proof sketch.** `Negligible.mul_pow` (twice, with `negligible_two_pow_neg` and
`(1/4)^N ≤ (1/2)^N`), `negligible_exp_neg_sqrt_div` with `C = 1` (`Nat.div_one`),
`Negligible.mono` and `Negligible.add`. -/
theorem negligible_colZKErr {εB : ℕ → ℝ} (hε : Negligible fun N => εB (Nat.sqrt N)) :
    Negligible fun N : ℕ => (N : ℝ) ^ 2 * εB (Nat.sqrt N) + Real.exp (-(Nat.sqrt N : ℝ)) +
      (N : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ N + (1 / 4 : ℝ) ^ N) + (1 / 4 : ℝ) ^ N := by
  have h2 : Negligible fun N : ℕ => (1 / 2 : ℝ) ^ N :=
    negligible_two_pow_neg.mono ⟨0, fun N _ => le_of_eq (by rw [one_div])⟩
  have h4 : Negligible fun N : ℕ => (1 / 4 : ℝ) ^ N := h2.mono ⟨0, fun N _ => by
    rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) N⟩
  have he : Negligible fun N : ℕ => Real.exp (-(Nat.sqrt N : ℝ)) :=
    (negligible_exp_neg_sqrt_div one_pos).mono ⟨0, fun N _ => le_of_eq (by rw [Nat.div_one])⟩
  have h24 : Negligible fun N : ℕ => (N : ℝ) ^ 2 * ((1 / 2 : ℝ) ^ N + (1 / 4 : ℝ) ^ N) :=
    ((h2.mul_pow 2).add (h4.mul_pow 2)).mono ⟨0, fun N _ => le_of_eq (by rw [mul_add])⟩
  exact (((hε.mul_pow 2).add he).add h24).add h4

/-! ### Splitting a search at an index -/

/-- **The first success splits at `k`**: the search over `List.finRange N` is the search before
`k`, else entry `k`, else the search after `k` (`CommitmentLemmas.ofFn_eq_append_cons` on
`List.finRange N`, `List.findSome?_append`). -/
theorem findSome?_finRange_split {α : Type*} {N : ℕ} (f : Fin N → Option α) (k : Fin N) :
    (List.finRange N).findSome? f =
      (((List.finRange k).findSome? fun i : Fin k => f (Fin.castLE k.2.le i)) <|> f k <|>
        (List.finRange (N - k - 1)).findSome? fun i : Fin (N - k - 1) => f ⟨k + 1 + i, by omega⟩) := by
  have h := CommitmentLemmas.ofFn_eq_append_cons (id : Fin N → Fin N) k
  rw [List.ofFn_id] at h
  rw [h, List.findSome?_append, List.findSome?_cons, List.ofFn_eq_map, List.ofFn_eq_map,
    List.findSome?_map, List.findSome?_map]
  simp only [Function.comp_def, id_eq]
  cases List.findSome? (fun i => f (Fin.castLE k.2.le i)) (List.finRange k) <;> cases f k <;> rfl

/-- **The first success splits at `k` into masked searches**: the search over `List.finRange N`
is the search masked to the indices before `k`, else entry `k`, else the search masked to the
indices after `k`.

**Proof sketch.** Split all three searches at `k` (`findSome?_finRange_split`). On the indices
before `k` the first mask is the identity and the second is `none`; on those after `k` the
reverse; at `k` both masks are `none`. The searches of `none` are `none`
(`List.findSome?_eq_none_iff`), and the remaining `<|>` chain is the original one. -/
theorem findSome?_finRange_split_lt {α : Type*} {N : ℕ} (f : Fin N → Option α) (k : Fin N) :
    (List.finRange N).findSome? f =
      (((List.finRange N).findSome? fun t : Fin N => if (t : ℕ) < k then f t else none) <|> f k <|>
        (List.finRange N).findSome? fun t : Fin N => if k < t then f t else none) := by
  rw [findSome?_finRange_split f k,
    findSome?_finRange_split (fun t : Fin N => if (t : ℕ) < k then f t else none) k,
    findSome?_finRange_split (fun t : Fin N => if k < t then f t else none) k]
  have h1 : (fun i : Fin k => if ((Fin.castLE k.2.le i : Fin N) : ℕ) < k then
      f (Fin.castLE k.2.le i) else none) = fun i : Fin k => f (Fin.castLE k.2.le i) :=
    funext fun i => if_pos (by simp)
  have h2 : (fun i : Fin (N - k - 1) => if (((⟨k + 1 + i, by omega⟩ : Fin N)) : ℕ) < k then
      f ⟨k + 1 + i, by omega⟩ else none) = fun _ => none :=
    funext fun i => if_neg (by simp only; omega)
  have h3 : (fun i : Fin k => if k < (Fin.castLE k.2.le i : Fin N) then
      f (Fin.castLE k.2.le i) else none) = fun _ => none :=
    funext fun i => if_neg (by rw [Fin.lt_def]; simp)
  have h4 : (fun i : Fin (N - k - 1) => if k < (⟨k + 1 + i, by omega⟩ : Fin N) then
      f ⟨k + 1 + i, by omega⟩ else none) = fun i : Fin (N - k - 1) => f ⟨k + 1 + i, by omega⟩ :=
    funext fun i => if_pos (by rw [Fin.lt_def]; simp only; omega)
  have hn : ∀ {M : ℕ}, (List.finRange M).findSome? (fun _ : Fin M => (none : Option α)) = none :=
    fun {M} => List.findSome?_eq_none_iff.2 fun _ _ => rfl
  rw [h1, h2, h3, h4, hn, hn, if_neg (lt_irrefl (k : ℕ)), if_neg (lt_irrefl k)]
  cases (List.finRange k).findSome? fun i : Fin k => f (Fin.castLE k.2.le i) <;> cases f k <;> rfl

end TCSlib.Cryptography.ColZK
