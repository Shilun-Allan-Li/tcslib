/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.FeedForwardCircuit
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Finset.BooleanAlgebra
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Logic.Equiv.Basic

open Finset
open scoped BigOperators

namespace ACP

open FeedForward

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The plain `AC₀` gate set: identity, NOT, and unbounded AND. -/
def AC_GateOps : Set (GateOp (Fin 2)) :=
  {GateOp.id (Fin 2),
   ⟨Fin 1, fun x ↦ 1 - x 0⟩} ∪
  ⋃ n, {⟨Fin n, fun x ↦ ∏ i, x i⟩}

/-- Count tuples satisfying a pointwise predicate. -/
lemma tuple_fail_count {ι : Type} [Fintype ι] [DecidableEq ι]
    {β : Type} [Fintype β] (P : β → Prop) [DecidablePred P] :
    (Finset.univ.filter (fun (f : ι → β) => ∀ i, P (f i))).card =
      (Finset.univ.filter P).card ^ Fintype.card ι := by
  classical
  let e : {f : ι → β // ∀ i, P (f i)} ≃ (ι → {b : β // P b}) :=
    { toFun := fun f i => ⟨f.1 i, f.2 i⟩
      invFun := fun g => ⟨fun i => (g i).1, fun i => (g i).2⟩
      left_inv := by
        intro f
        cases f
        rfl
      right_inv := by
        intro g
        rfl }
  calc
    (Finset.univ.filter (fun (f : ι → β) => ∀ i, P (f i))).card
        = Fintype.card {f : ι → β // ∀ i, P (f i)} := by
            symm
            exact Fintype.card_subtype (fun f : ι → β => ∀ i, P (f i))
    _ = Fintype.card (ι → {b : β // P b}) := Fintype.card_congr e
    _ = Fintype.card {b : β // P b} ^ Fintype.card ι := by
          rw [Fintype.card_fun]
    _ = (Finset.univ.filter P).card ^ Fintype.card ι := by
          rw [Fintype.card_subtype P]

/-- Averaging lemma for the probabilistic method. -/
lemma prob_method_averaging {α β : Type*} [Fintype α] [DecidableEq α]
    [Fintype β] [Nonempty β]
    (Bad : Finset α) (Fail : α → β → Prop) [∀ a b, Decidable (Fail a b)]
    (C : ℕ)
    (h_prob : ∀ a ∈ Bad, (univ.filter (Fail a ·)).card * C ≤ Fintype.card β) :
    ∃ (b : β), (univ.filter (fun a => a ∈ Bad ∧ Fail a b)).card * C ≤ Bad.card := by
  by_contra! h
  have h_sum :
      ∑ b : β, (Finset.card (Finset.filter (fun a => a ∈ Bad ∧ Fail a b) Finset.univ)) =
        ∑ a ∈ Bad, (Finset.card (Finset.filter (fun b => Fail a b) Finset.univ)) := by
    simp only [card_filter]
    rw [Finset.sum_comm]
    rw [← Finset.sum_subset (Finset.subset_univ Bad)] <;> aesop
  have := Finset.sum_le_sum fun b (_ : b ∈ Finset.univ) => Nat.mul_le_mul_right C (h b)
  simp_all [← Finset.sum_mul _ _ _]
  have h_combined : Fintype.card β * (Bad.card + 1) ≤ (∑ a ∈ Bad, #{b : β | Fail a b}) * C := by
    cases C <;> aesop
  have h_combined : (∑ a ∈ Bad, #{b : β | Fail a b}) * C ≤ Fintype.card β * Bad.card := by
    exact le_trans (Finset.sum_mul _ _ _ |> le_of_eq)
      (by simpa [mul_comm] using Finset.sum_le_sum fun a ha => h_prob a ha)
  nlinarith [Fintype.card_pos_iff.mpr ‹_›]

/-- Booleanization of a field element. Use only on values in `{0,1}`. -/
def bitify (a : ZMod p) : Fin 2 :=
  if a = 1 then 1 else 0

lemma cast_bitify_eq {a : ZMod p} (ha : a ∈ ({0, 1} : Set (ZMod p))) :
    ((((bitify (p := p) a : Fin 2) : Nat) : ZMod p)) = a := by
  have hp1 : 1 < p := by exact (Fact.out : Nat.Prime p).one_lt
  simp [bitify] at ha ⊢
  rcases ha with rfl | rfl
  · simp
  · simp

lemma one_sub_pow_card_sub_one (a : ZMod p) :
    (1 - a ^ (p - 1) : ZMod p) = if a = 0 then 1 else 0 := by
  by_cases ha : a = 0
  · simp [ha]
    have hlt : 1 < p := (Fact.out : Nat.Prime p).one_lt
    omega
  · rw [ZMod.pow_card_sub_one_eq_one (p := p) ha]
    simp [ha]

lemma bit_indicator_eq_bitify {a : ZMod p} (ha : a ∈ ({0, 1} : Set (ZMod p))) :
    (1 - (1 - a) ^ (p - 1) : ZMod p) =
      ((((bitify (p := p) a : Fin 2) : Nat) : ZMod p)) := by
  have hp1 : 1 < p := (Fact.out : Nat.Prime p).one_lt
  simp [bitify] at ha ⊢
  rcases ha with rfl | rfl
  · simp
  · simp
    omega

/-- Unbounded `MOD p` on Boolean inputs. -/
def modGateOp (width : ℕ) : GateOp (Fin 2) where
  ι := Fin width
  func x := if (∑ i, (((x i : Fin 2) : Nat) : ZMod p)) = 0 then 1 else 0

/-- `AC⁰[p]` gates: identity, NOT, unbounded AND, and unbounded `MOD p`. -/
def ACp_GateOps : Set (GateOp (Fin 2)) :=
  AC_GateOps ∪ ⋃ n, {modGateOp p n}

/-- Randomized OR-approximation over `ZMod p`. -/
noncomputable def approxOr {vars width ℓ : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p))
    (S : Fin ℓ → Finset (Fin width)) : MvPolynomial (Fin vars) (ZMod p) :=
  1 - ∏ k, (1 - (∑ i ∈ S k, polys i) ^ (p - 1))

/-- Exact `MOD p` polynomial over `ZMod p`. -/
noncomputable def exactMod {vars width : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)) :
    MvPolynomial (Fin vars) (ZMod p) :=
  1 - (∑ i, polys i) ^ (p - 1)

/-- Value-level version of `approxOr`. -/
def approxOr_val {width ℓ : ℕ}
    (v : Fin width → ZMod p) (S : Fin ℓ → Finset (Fin width)) : ZMod p :=
  1 - ∏ k, (1 - (∑ i ∈ S k, v i) ^ (p - 1))

/-- Value-level OR detector over `ZMod p`. -/
def OR_val {width : ℕ} (v : Fin width → ZMod p) : ZMod p :=
  1 - ∏ k, (1 - (v k) ^ (p - 1))

/-- `approxOr` multiplies degree by at most `(p-1)ℓ`. -/
theorem approxOr_totalDegree (vars width ℓ : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p))
    (S : Fin ℓ → Finset (Fin width)) :
    (approxOr p polys S).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree := by
  have h_term (k) :
      (1 - (∑ i ∈ S k, polys i) ^ (p - 1)).totalDegree ≤
        (p - 1) * (⨆ i, (polys i).totalDegree) := by
    grw [MvPolynomial.totalDegree_sub]
    simp only [MvPolynomial.totalDegree_one, zero_le, sup_of_le_right]
    grw [MvPolynomial.totalDegree_pow]
    refine mul_le_mul_of_nonneg_left ?_ (Nat.zero_le _)
    grw [MvPolynomial.totalDegree_finsetSum_le]
    intro i hi
    exact le_ciSup (Set.finite_range (polys · |>.totalDegree) |> Set.Finite.bddAbove) i
  trans ∑ k, (1 - (∑ i ∈ S k, polys i) ^ (p - 1)).totalDegree
  · grw [approxOr, MvPolynomial.totalDegree_sub, MvPolynomial.totalDegree_finset_prod]
    simp
  · grw [Finset.sum_le_sum fun i _ ↦ h_term i]
    simp [mul_assoc, mul_comm]

/-- `exactMod` multiplies degree by at most `p-1`. -/
theorem exactMod_totalDegree (vars width : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)) :
    (exactMod p polys).totalDegree ≤ (p - 1) * ⨆ i, (polys i).totalDegree := by
  grw [exactMod, MvPolynomial.totalDegree_sub]
  simp only [MvPolynomial.totalDegree_one, zero_le, sup_of_le_right]
  grw [MvPolynomial.totalDegree_pow]
  refine mul_le_mul_of_nonneg_left ?_ (Nat.zero_le _)
  grw [MvPolynomial.totalDegree_finsetSum_le]
  intro i hi
  exact le_ciSup (Set.finite_range (polys · |>.totalDegree) |> Set.Finite.bddAbove) i

/-- For a nonzero vector, at most half of all subsets have subset-sum `0`. -/
lemma subset_sum_zero_bound {n : ℕ} (v : Fin n → ZMod p) (hv : v ≠ 0) :
    2 * (Finset.univ.filter (fun s : Finset (Fin n) => ∑ i ∈ s, v i = 0)).card ≤
      (Finset.univ : Finset (Finset (Fin n))).card := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
  have h_pairs :
      Finset.card (Finset.filter (fun s => ∑ i ∈ s, v i = 0)
        (Finset.powerset (Finset.univ : Finset (Fin n))))
      ≤
      Finset.card (Finset.filter (fun s => ∑ i ∈ s, v i ≠ 0)
        (Finset.powerset (Finset.univ : Finset (Fin n)))) := by
    have h_pairs :
        Finset.filter (fun s => ∑ i ∈ s, v i = 0)
            (Finset.powerset (Finset.univ : Finset (Fin n)))
          ⊆
        Finset.image (fun s => if i ∈ s then s \ {i} else s ∪ {i})
          (Finset.filter (fun s => ∑ i ∈ s, v i ≠ 0)
            (Finset.powerset (Finset.univ : Finset (Fin n)))) := by
      intro s hs
      simp_all
      use if i ∈ s then s \ {i} else Insert.insert i s
      aesop
    exact le_trans (Finset.card_le_card h_pairs) (Finset.card_image_le)
  have := Finset.card_add_card_compl
    (Finset.filter (fun s : Finset (Fin n) => ∑ i ∈ s, v i = 0)
      (Finset.powerset (Finset.univ : Finset (Fin n))))
  simp_all [Finset.filter_not, Finset.card_sdiff]
  linarith

lemma approxOr_eval_eq {vars width ℓ : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p))
    (S : Fin ℓ → Finset (Fin width)) (y : Fin vars → ZMod p) :
    (approxOr p polys S).eval y = approxOr_val p (fun i ↦ (polys i).eval y) S := by
  unfold approxOr approxOr_val
  aesop

lemma approxOr_failure_iff {width ℓ : ℕ}
    (v : Fin width → ZMod p) (S : Fin ℓ → Finset (Fin width)) :
    approxOr_val p v S ≠ OR_val p v ↔ (v ≠ 0 ∧ ∀ k, ∑ i ∈ S k, v i = 0) := by
  by_cases hv : v = 0
  · subst hv
    simp [approxOr_val, OR_val, one_sub_pow_card_sub_one]
  · constructor
    · intro h
      refine ⟨hv, ?_⟩
      intro k
      by_contra hk
      have hA : approxOr_val p v S = 1 := by
        unfold approxOr_val
        have hk0 : (1 - (∑ i ∈ S k, v i) ^ (p - 1) : ZMod p) = 0 := by
          simp [one_sub_pow_card_sub_one, hk]
        rw [Finset.prod_eq_zero (Finset.mem_univ k) hk0]
        simp
      have hO : OR_val p v = 1 := by
        obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
        unfold OR_val
        have hk0 : (1 - (v k) ^ (p - 1) : ZMod p) = 0 := by
          simpa [one_sub_pow_card_sub_one, hk]
        rw [Finset.prod_eq_zero (Finset.mem_univ k) hk0]
        simp
      exact h (by rw [hA, hO])
    · rintro ⟨hv, hsum_zero⟩
      have hA : approxOr_val p v S = 0 := by
        unfold approxOr_val
        simp [one_sub_pow_card_sub_one, hsum_zero]
      have hO : OR_val p v = 1 := by
        obtain ⟨k, hk⟩ := Function.ne_iff.mp hv
        unfold OR_val
        have hk0 : (1 - (v k) ^ (p - 1) : ZMod p) = 0 := by
          simpa [one_sub_pow_card_sub_one, hk]
        rw [Finset.prod_eq_zero (Finset.mem_univ k) hk0]
        simp
      rw [hA, hO]
      norm_num

lemma count_bad_S {width ℓ : ℕ} (v : Fin width → ZMod p) (hv : v ≠ 0) :
    (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
      approxOr_val p v S ≠ OR_val p v)).card * 2 ^ ℓ ≤
      Fintype.card (Fin ℓ → Finset (Fin width)) := by
  simp[approxOr_failure_iff, hv]
  have htuple :
    #{S : Fin ℓ → Finset (Fin width) | ∀ k : Fin ℓ, ∑ i ∈ S k, v i = 0} =
      (#{T : Finset (Fin width) | ∑ i ∈ T, v i = 0}) ^ ℓ := by
        classical
        let P : Finset (Fin width) → Prop := fun T => ∑ i ∈ T, v i = 0
        have hcard :
            Fintype.card {S : Fin ℓ → Finset (Fin width) // ∀ k : Fin ℓ, P (S k)} =
              (Fintype.card {T : Finset (Fin width) // P T}) ^ ℓ := by
          let e :
              {S : Fin ℓ → Finset (Fin width) // ∀ k : Fin ℓ, P (S k)} ≃
                (Fin ℓ → {T : Finset (Fin width) // P T}) :=
            { toFun := fun S k => ⟨S.1 k, S.2 k⟩
              invFun := fun f => ⟨fun k => (f k).1, fun k => (f k).2⟩
              left_inv := by
                intro S
                cases S
                rfl
              right_inv := by
                intro f
                rfl }
          rw [Fintype.card_congr e, Fintype.card_fun, Fintype.card_fin]
        have hleft :
            #{S : Fin ℓ → Finset (Fin width) | ∀ k : Fin ℓ, ∑ i ∈ S k, v i = 0} =
              Fintype.card {S : Fin ℓ → Finset (Fin width) // ∀ k : Fin ℓ, P (S k)} := by
          simp [P]
          symm
          simpa using
            (Fintype.card_subtype (fun S : Fin ℓ → Finset (Fin width) =>
              ∀ k : Fin ℓ, ∑ i ∈ S k, v i = 0))
        have hright :
            #{T : Finset (Fin width) | ∑ i ∈ T, v i = 0} =
              Fintype.card {T : Finset (Fin width) // P T} := by
          simp [P]
          symm
          simpa using
            (Fintype.card_subtype (fun S : Finset (Fin width) => ∑ i ∈ S, v i = 0))
        rw [hleft, hright]
        exact hcard
  simp [htuple]
  rw [← Nat.mul_pow]
  have hmain : #{T : Finset (Fin width) | ∑ i ∈ T, v i = 0} * 2 ≤ 2 ^ width := by
    have h_nz : ∃ i : Fin width, ¬ v i = 0 := by
      by_contra h
      apply hv
      funext i
      by_contra hi
      exact h ⟨i, hi⟩
    rcases h_nz with ⟨t, ht⟩
    let toggle_t (T : Finset (Fin width)) : Finset (Fin width) := if t ∈ T then erase T t else insert t T
    have h_toggle_t_invol : Function.Involutive toggle_t := by
      intro T
      by_cases ht : t ∈ T
      · calc
          toggle_t (toggle_t T)
              = toggle_t (erase T t) := by
                  simp [toggle_t, ht]
          _ = insert t (erase T t) := by
                have hnot : t ∉ erase T t := by simp
                simp [toggle_t, hnot]
          _ = T := Finset.insert_erase ht
      · calc
          toggle_t (toggle_t T)
              = toggle_t (insert t T) := by
                  simp [toggle_t, ht]
          _ = erase (insert t T) t := by
                have hmem : t ∈ insert t T := by simp
                simp [toggle_t, hmem]
          _ = T := Finset.erase_insert ht
    have lem_toggle_sum : ∑ T : Finset (Fin width), (if ∑ i ∈ T, v i = 0 then 1 else 0) = ∑ T : Finset (Fin width), (if ∑ i ∈ toggle_t T, v i = 0 then 1 else 0) := by
      classical
      let e : Equiv.Perm (Finset (Fin width)) :=
        { toFun := toggle_t
          invFun := toggle_t
          left_inv := h_toggle_t_invol
          right_inv := h_toggle_t_invol }
      have hsum :
          ∑ T : Finset (Fin width), (if ∑ i ∈ T, v i = 0 then 1 else 0) =
            ∑ T : Finset (Fin width), (if ∑ i ∈ e T, v i = 0 then 1 else 0) :=
        (Equiv.sum_comp e (fun T : Finset (Fin width) =>
          if ∑ i ∈ T, v i = 0 then 1 else 0)).symm
      simpa only [e] using hsum
    have lem_pair (T : Finset (Fin width)) : (if ∑ i ∈ T, v i = 0 then 1 else 0) + (if ∑ i ∈ toggle_t T, v i = 0 then 1 else 0) ≤ 1 := by
      by_cases hT : ∑ i ∈ T, v i = 0
      · simp [hT]
        intro hc
        by_cases htT : t ∈ T
        · have h1 : (∑ i ∈ T.erase t, v i) + v t = 0 := by
            simpa [hT] using (Finset.sum_erase_add (s := T) (a := t) (f := v) htT)
          have h2 : (∑ i ∈ T.erase t, v i) = 0 := by
            have h21 : toggle_t T = T.erase t := by
              simp [toggle_t, htT]
            rw [h21] at hc
            exact hc
          have h3 : v t = 0 := by
            rw [h2] at h1
            simpa using h1
          exact ht h3
        · have h1 : (∑ i ∈ insert t T, v i) - v t = 0 := by
            simp [Finset.sum_insert, htT, hT]
          have h2 : (∑ i ∈ insert t T, v i) = 0 := by
            have h21 : toggle_t T = insert t T := by
              simp [toggle_t, htT]
            rw [h21] at hc
            exact hc
          have h3 : v t = 0 := by
            rw [h2] at h1
            simpa using h1
          exact ht h3
      · by_cases h : ∑ i ∈ toggle_t T, v i = 0
        · simp [h, hT]
        · simp [h, hT]
    calc
      #{T : Finset (Fin width) | ∑ i ∈ T, v i = 0} * 2 = 2 * ∑ T : Finset (Fin width), if ∑ i ∈ T, v i = 0 then 1 else 0 := by
        simp
        omega
      _ = ∑ T : Finset (Fin width), (if ∑ i ∈ T, v i = 0 then 1 else 0) + ∑ T : Finset (Fin width), (if ∑ i ∈ toggle_t T, v i = 0 then 1 else 0) := by
        simp only [lem_toggle_sum]
        omega
      _ = ∑ T : Finset (Fin width), ((if ∑ i ∈ T, v i = 0 then 1 else 0) + (if ∑ i ∈ toggle_t T, v i = 0 then 1 else 0)) := by
        rw [Finset.sum_add_distrib]
      _ ≤ ∑ T : Finset (Fin width), 1 := by
        apply Finset.sum_le_sum
        intro T hT
        exact lem_pair T
      _ = 2 ^ width := by
        simp
  exact Nat.pow_le_pow_left hmain ℓ


/-- The number of random seeds for the `ℓ` independent subset choices. -/
lemma approxSeed_card (width ℓ : ℕ) :
    Fintype.card (Fin ℓ → Finset (Fin width)) = 2 ^ (width * ℓ) := by
  calc
    Fintype.card (Fin ℓ → Finset (Fin width))
        = (Fintype.card (Finset (Fin width))) ^ ℓ := by
            simp
    _ = (2 ^ width) ^ ℓ := by
          simp
    _ = 2 ^ (width * ℓ) := by
          rw [← Nat.pow_mul]

/-- Pointwise bad-seed bound for the randomized OR approximator. -/
lemma count_bad_S_or {width ℓ : ℕ} (v : Fin width → ZMod p) :
    (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
      approxOr_val p v S ≠ OR_val p v)).card * 2 ^ ℓ ≤
      Fintype.card (Fin ℓ → Finset (Fin width)) := by
  by_cases hv : v = 0
  · simp [approxOr_failure_iff (p := p), hv]
  · exact count_bad_S (p := p) v hv

/-- The canonical list of all OR-approximating polynomials, one per random seed.

The list has length `2^(width * ℓ)`.  It is a list rather than a set, so if two
random seeds produce the same polynomial, that polynomial appears with the
corresponding multiplicity. -/
noncomputable def approxOrPolyList {vars width ℓ : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)) :
    List (MvPolynomial (Fin vars) (ZMod p)) :=
  (Finset.univ : Finset (Fin ℓ → Finset (Fin width))).toList.map
    (fun S => approxOr p polys S)

lemma approxOrPolyList_length {vars width ℓ : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)) :
    (approxOrPolyList (p := p) (ℓ := ℓ) polys).length = 2 ^ (width * ℓ) := by
  classical
  calc
    (approxOrPolyList (p := p) (ℓ := ℓ) polys).length
        = Fintype.card (Fin ℓ → Finset (Fin width)) := by
            simp [approxOrPolyList]
    _ = 2 ^ (width * ℓ) := approxSeed_card width ℓ

/-- For each fixed input, at most a `2^{-ℓ}` fraction of the OR-list entries fail. -/
theorem approxOr_pointwise_bad_count (vars width ℓ : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p))
    (y : Fin vars → ZMod p) :
    (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
      (approxOr p polys S).eval y ≠
        1 - ∏ k, (1 - ((polys k).eval y) ^ (p - 1)))).card * 2 ^ ℓ ≤
      2 ^ (width * ℓ) := by
  calc
    (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
      (approxOr p polys S).eval y ≠
        1 - ∏ k, (1 - ((polys k).eval y) ^ (p - 1)))).card * 2 ^ ℓ
        ≤ Fintype.card (Fin ℓ → Finset (Fin width)) := by
            simpa [approxOr_eval_eq, OR_val] using
              (count_bad_S_or (p := p) (ℓ := ℓ)
                (v := fun i => MvPolynomial.eval y (polys i)))
    _ = 2 ^ (width * ℓ) := approxSeed_card width ℓ

/-- Pointwise-distribution version for OR: all random seeds give a list of
`2^(width * ℓ)` low-degree polynomials, and every fixed input is bad for at most
a `2^{-ℓ}` fraction of the entries. -/
theorem exists_good_approxOr (vars width ℓ : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)) :
    ∃ (Ps : List (MvPolynomial (Fin vars) (ZMod p))),
      Ps = approxOrPolyList (p := p) (ℓ := ℓ) polys ∧
      Ps.length = 2 ^ (width * ℓ) ∧
      (∀ P ∈ Ps, P.totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree) ∧
      ∀ y : Fin vars → ZMod p,
        (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
          (approxOr p polys S).eval y ≠
            1 - ∏ k, (1 - ((polys k).eval y) ^ (p - 1)))).card * 2 ^ ℓ ≤
          Ps.length := by
  classical
  refine ⟨approxOrPolyList (p := p) (ℓ := ℓ) polys, rfl,
    approxOrPolyList_length (p := p) (ℓ := ℓ) polys, ?_, ?_⟩
  · intro P hP
    rw [approxOrPolyList] at hP
    rcases List.mem_map.mp hP with ⟨S, hS, hPS⟩
    rw [← hPS]
    exact approxOr_totalDegree (p := p) vars width ℓ polys S
  · intro y
    calc
      (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
        (approxOr p polys S).eval y ≠
          1 - ∏ k, (1 - ((polys k).eval y) ^ (p - 1)))).card * 2 ^ ℓ
          ≤ 2 ^ (width * ℓ) :=
            approxOr_pointwise_bad_count (p := p) vars width ℓ polys y
      _ = (approxOrPolyList (p := p) (ℓ := ℓ) polys).length :=
          (approxOrPolyList_length (p := p) (ℓ := ℓ) polys).symm

/-- De Morgan turns the OR-approximator into an AND-approximator. -/
noncomputable def approxAnd {vars width ℓ : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p))
    (S : Fin ℓ → Finset (Fin width)) : MvPolynomial (Fin vars) (ZMod p) :=
  1 - approxOr p (fun i => 1 - polys i) S

/-- `approxAnd` has the same degree bound as `approxOr`. -/
theorem approxAnd_totalDegree (vars width ℓ : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p))
    (S : Fin ℓ → Finset (Fin width)) :
    (approxAnd p polys S).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree := by
  unfold approxAnd
  have := approxOr_totalDegree (p := p) vars width ℓ (fun i => 1 - polys i) S
  refine le_trans (MvPolynomial.totalDegree_sub _ _) (max_le ?_ ?_)
  · simp
  · refine le_trans this (mul_le_mul_of_nonneg_left (ciSup_mono ?_ ?_) (Nat.zero_le _))
    · exact Set.finite_range _ |> Set.Finite.bddAbove
    · intro i
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      simp

/-- The canonical list of all AND-approximating polynomials, one per random seed. -/
noncomputable def approxAndPolyList {vars width ℓ : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)) :
    List (MvPolynomial (Fin vars) (ZMod p)) :=
  (Finset.univ : Finset (Fin ℓ → Finset (Fin width))).toList.map
    (fun S => approxAnd p polys S)

lemma approxAndPolyList_length {vars width ℓ : ℕ}
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)) :
    (approxAndPolyList (p := p) (ℓ := ℓ) polys).length = 2 ^ (width * ℓ) := by
  classical
  calc
    (approxAndPolyList (p := p) (ℓ := ℓ) polys).length
        = Fintype.card (Fin ℓ → Finset (Fin width)) := by
            simp [approxAndPolyList]
    _ = 2 ^ (width * ℓ) := approxSeed_card width ℓ

/-- For each fixed input, at most a `2^{-ℓ}` fraction of the AND-list entries fail. -/
theorem approxAnd_pointwise_bad_count (vars width ℓ : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p))
    (y : Fin vars → ZMod p) :
    (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
      (approxAnd p polys S).eval y ≠
        ∏ k, (1 - (1 - (polys k).eval y) ^ (p - 1)))).card * 2 ^ ℓ ≤
      2 ^ (width * ℓ) := by
  have h := approxOr_pointwise_bad_count (p := p) vars width ℓ (fun i => 1 - polys i) y
  have hfilter :
      (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
        (approxAnd p polys S).eval y ≠
          ∏ k, (1 - (1 - (polys k).eval y) ^ (p - 1)))) =
      (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
        (approxOr p (fun i ↦ 1 - polys i) S).eval y ≠
          1 - ∏ k, (1 - ((1 - polys k).eval y) ^ (p - 1)))) := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hbad
      by_contra hgood
      have hgood' :
          (approxOr p (fun i ↦ 1 - polys i) S).eval y =
            1 - ∏ k, (1 - ((1 - polys k).eval y) ^ (p - 1)) := by
        simpa using hgood
      apply hbad
      have h' := congrArg (fun z : ZMod p => 1 - z) hgood'
      simpa [approxAnd] using h'
    · intro hbad
      by_contra hgood
      have hgood' :
          (approxAnd p polys S).eval y =
            ∏ k, (1 - (1 - (polys k).eval y) ^ (p - 1)) := by
        simpa using hgood
      apply hbad
      have h' := congrArg (fun z : ZMod p => 1 - z) hgood'
      simpa [approxAnd] using h'
  rw [hfilter]
  exact h

/-- Pointwise-distribution version for AND. -/
theorem exists_good_approxAnd (vars width ℓ : ℕ)
    (polys : (i : Fin width) → MvPolynomial (Fin vars) (ZMod p)) :
    ∃ (Ps : List (MvPolynomial (Fin vars) (ZMod p))),
      Ps = approxAndPolyList (p := p) (ℓ := ℓ) polys ∧
      Ps.length = 2 ^ (width * ℓ) ∧
      (∀ P ∈ Ps, P.totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree) ∧
      ∀ y : Fin vars → ZMod p,
        (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
          (approxAnd p polys S).eval y ≠
            ∏ k, (1 - (1 - (polys k).eval y) ^ (p - 1)))).card * 2 ^ ℓ ≤
          Ps.length := by
  classical
  refine ⟨approxAndPolyList (p := p) (ℓ := ℓ) polys, rfl,
    approxAndPolyList_length (p := p) (ℓ := ℓ) polys, ?_, ?_⟩
  · intro P hP
    rw [approxAndPolyList] at hP
    rcases List.mem_map.mp hP with ⟨S, hS, hPS⟩
    rw [← hPS]
    exact approxAnd_totalDegree (p := p) vars width ℓ polys S
  · intro y
    calc
      (Finset.univ.filter (fun S : Fin ℓ → Finset (Fin width) =>
        (approxAnd p polys S).eval y ≠
          ∏ k, (1 - (1 - (polys k).eval y) ^ (p - 1)))).card * 2 ^ ℓ
          ≤ 2 ^ (width * ℓ) :=
            approxAnd_pointwise_bad_count (p := p) vars width ℓ polys y
      _ = (approxAndPolyList (p := p) (ℓ := ℓ) polys).length :=
          (approxAndPolyList_length (p := p) (ℓ := ℓ) polys).symm

lemma ACp_GateOps_cases {op : GateOp (Fin 2)} (h : op ∈ ACp_GateOps p) :
    op = ⟨PUnit, fun x ↦ x PUnit.unit⟩ ∨
    op = ⟨Fin 1, fun x ↦ 1 - x 0⟩ ∨
    (∃ n, op = ⟨Fin n, fun x ↦ ∏ i, x i⟩) ∨
    (∃ n, op = modGateOp p n) := by
  unfold ACp_GateOps at h
  unfold AC_GateOps at h
  rcases h with h | h
  · rcases h with h | h
    · simp [GateOp.id] at h
      rcases h with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
    · rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
      exact Or.inr <| Or.inr <| Or.inl ⟨n, hn⟩
  · rcases Set.mem_iUnion.mp h with ⟨n, hn⟩
    exact Or.inr <| Or.inr <| Or.inr ⟨n, hn⟩

lemma exactMod_on_bits {width : ℕ} (inputs : Fin width → ZMod p)
    (hinputs : ∀ i, inputs i ∈ ({0, 1} : Set (ZMod p))) :
    (1 - (∑ i, inputs i) ^ (p - 1) : ZMod p) =
      ((modGateOp p width).func (fun i ↦ bitify (p := p) (inputs i)) : Nat) := by
  have hs :
      ∑ i, ((((bitify (p := p) (inputs i) : Fin 2) : Nat) : ZMod p)) = ∑ i, inputs i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using cast_bitify_eq (p := p) (hinputs i)
  rw [show (1 - (∑ i, inputs i) ^ (p - 1) : ZMod p) = if ∑ i, inputs i = 0 then 1 else 0 by
    simpa using one_sub_pow_card_sub_one (p := p) (∑ i, inputs i)]
  simp [modGateOp, hs]
  split_ifs <;> norm_num

lemma exactAnd_on_bits {width : ℕ} (inputs : Fin width → ZMod p)
    (hinputs : ∀ i, inputs i ∈ ({0, 1} : Set (ZMod p))) :
    (∏ i, (1 - (1 - inputs i) ^ (p - 1)) : ZMod p) =
      ((∏ i, bitify (p := p) (inputs i) : Fin 2) : Nat) := by
  by_cases hzero : ∃ i, inputs i = 0
  · rcases hzero with ⟨i, hi⟩
    have hleft : (∏ j, (1 - (1 - inputs j) ^ (p - 1)) : ZMod p) = 0 := by
      rw [← Finset.mul_prod_erase
        (s := (Finset.univ : Finset (Fin width)))
        (a := i)
        (f := fun j : Fin width ↦ ((1 - (1 - inputs j) ^ (p - 1)) : ZMod p))
        (by simp)]
      simp [hi]
    have hright_fin : (∏ j, bitify (p := p) (inputs j) : Fin 2) = 0 := by
      rw [← Finset.mul_prod_erase
        (s := (Finset.univ : Finset (Fin width)))
        (a := i)
        (f := fun j : Fin width ↦ bitify (p := p) (inputs j))
        (by simp)]
      simp [hi, bitify]
    have hright : ((∏ j, bitify (p := p) (inputs j) : Fin 2) : Nat) = 0 := by
      simp [hright_fin]
    simp [hleft, hright]
  · have hall : ∀ i, inputs i = 1 := by
      intro i
      have hi := hinputs i
      simp at hi
      rcases hi with h0 | h1
      · exfalso
        exact hzero ⟨i, h0⟩
      · exact h1
    have hp1 : p - 1 ≠ 0 := by
      have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
      omega
    have hleft : (∏ j, (1 - (1 - inputs j) ^ (p - 1)) : ZMod p) = 1 := by
      simp [hall, hp1]
    have hright_fin : (∏ j, bitify (p := p) (inputs j) : Fin 2) = 1 := by
      simp [hall, bitify]
    have hright : ((∏ j, bitify (p := p) (inputs j) : Fin 2) : Nat) = 1 := by
      simp [hright_fin]
    simp [hleft, hright]

lemma exists_poly_for_gate {n ℓ : ℕ}
    (op : GateOp (Fin 2)) (hop : op ∈ ACp_GateOps p)
    (polys : op.ι → MvPolynomial (Fin n) (ZMod p)) :
    ∃ (Seed : Type) (_ : Fintype Seed) (_ : DecidableEq Seed)
      (P : Seed → MvPolynomial (Fin n) (ZMod p)),
      0 < Fintype.card Seed ∧
      (∀ s, (P s).totalDegree ≤ (p - 1) * ℓ * ⨆ i, (polys i).totalDegree) ∧
      ∀ x : Fin n → Fin 2,
        let y : Fin n → ZMod p := fun j ↦ ((x j : Nat) : ZMod p)
        let inputs := fun i ↦ (polys i).eval y
        (∀ i, inputs i ∈ ({0, 1} : Set (ZMod p))) →
        (Finset.univ.filter (fun s : Seed =>
          (P s).eval y ≠
            (op.func (fun i ↦ bitify (p := p) (inputs i)) : Nat))).card * 2 ^ ℓ ≤
          Fintype.card Seed := by
  classical
  by_cases hℓ : ℓ = 0
  · subst ℓ
    refine ⟨PUnit, inferInstance, inferInstance,
      (fun _ => (0 : MvPolynomial (Fin n) (ZMod p))), ?_, ?_, ?_⟩
    · simp
    · intro s
      simp
    · intro x
      dsimp
      intro hbits
      simpa using
        (Finset.card_le_univ (Finset.univ.filter (fun s : PUnit =>
          ((0 : MvPolynomial (Fin n) (ZMod p)).eval
              (fun j ↦ ((x j : Nat) : ZMod p))) ≠
            (op.func (fun i ↦ bitify (p := p)
              ((polys i).eval (fun j ↦ ((x j : Nat) : ZMod p)))) : Nat))))
  · have hℓ1 : 1 ≤ ℓ := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hℓ)
    have hmul : 1 ≤ (p - 1) * ℓ := by
      have hp : 1 < p := (Fact.out : Nat.Prime p).one_lt
      have hp' : 0 < p - 1 := by omega
      exact Nat.succ_le_of_lt (Nat.mul_pos hp' (Nat.pos_of_ne_zero hℓ))
    rcases ACp_GateOps_cases (p := p) hop with hId | hNot | hAnd | hMod
    · subst hId
      refine ⟨PUnit, inferInstance, inferInstance, (fun _ => polys PUnit.unit), ?_, ?_, ?_⟩
      · simp
      · intro s
        have hsup : (⨆ i, (polys i).totalDegree) = (polys PUnit.unit).totalDegree := by
          simp
        rw [hsup]
        simpa [one_mul, mul_assoc] using
          (Nat.mul_le_mul_right (polys PUnit.unit).totalDegree hmul)
      · intro x
        dsimp
        intro hbits
        have hcorrect :
            (polys PUnit.unit).eval (fun j ↦ ((x j : Nat) : ZMod p)) =
              (bitify (p := p)
                ((polys PUnit.unit).eval (fun j ↦ ((x j : Nat) : ZMod p))) : Nat) := by
          simpa using (cast_bitify_eq (p := p) (hbits PUnit.unit)).symm
        have hfilter :
            (Finset.univ.filter (fun s : PUnit =>
              (polys PUnit.unit).eval (fun j ↦ ((x j : Nat) : ZMod p)) ≠
                (bitify (p := p)
                  ((polys PUnit.unit).eval (fun j ↦ ((x j : Nat) : ZMod p))) : Nat))) = ∅ := by
          ext s
          constructor
          · intro hs
            exact False.elim ((Finset.mem_filter.mp hs).2 hcorrect)
          · intro hs
            exact False.elim (by simp at hs)
        rw [hfilter]
        simp
    · subst hNot
      refine ⟨PUnit, inferInstance, inferInstance, (fun _ => 1 - polys 0), ?_, ?_, ?_⟩
      · simp
      · intro s
        have hdeg0 : (1 - polys 0).totalDegree ≤ (polys 0).totalDegree := by
          simpa using
            (MvPolynomial.totalDegree_sub (1 : MvPolynomial (Fin n) (ZMod p)) (polys 0))
        have hsup : (polys 0).totalDegree ≤ ⨆ i, (polys i).totalDegree := by
          exact le_ciSup (Set.finite_range (polys · |>.totalDegree) |> Set.Finite.bddAbove) 0
        calc
          (1 - polys 0).totalDegree ≤ (polys 0).totalDegree := hdeg0
          _ ≤ 1 * (⨆ i, (polys i).totalDegree) := by
            simp [one_mul]
          _ ≤ ((p - 1) * ℓ) * (⨆ i, (polys i).totalDegree) := by
            simpa [one_mul] using Nat.mul_le_mul_right (⨆ i, (polys i).totalDegree) hmul
          _ = (p - 1) * ℓ * (⨆ i, (polys i).totalDegree) := by
            simp [mul_assoc]
      · intro x
        dsimp
        intro hbits
        have hcorrect :
            (1 - polys 0).eval (fun j ↦ ((x j : Nat) : ZMod p)) =
              ((1 - bitify (p := p)
                ((polys 0).eval (fun j ↦ ((x j : Nat) : ZMod p))) : Fin 2) : Nat) := by
          have h0 := hbits 0
          simp at h0
          rcases h0 with h0 | h1
          · simp [h0, bitify]
          · simp [h1, bitify]
        have hfilter :
            (Finset.univ.filter (fun s : PUnit =>
              (1 - polys 0).eval (fun j ↦ ((x j : Nat) : ZMod p)) ≠
                ((1 - bitify (p := p)
                  ((polys 0).eval (fun j ↦ ((x j : Nat) : ZMod p))) : Fin 2) : Nat))) = ∅ := by
          ext s
          constructor
          · intro hs
            exact False.elim ((Finset.mem_filter.mp hs).2 hcorrect)
          · intro hs
            exact False.elim (by simp at hs)
        rw [hfilter]
        simp
    · rcases hAnd with ⟨width, rfl⟩
      refine ⟨Fin ℓ → Finset (Fin width), inferInstance, inferInstance,
        (fun S => approxAnd p polys S), ?_, ?_, ?_⟩
      · simp
      · intro S
        exact approxAnd_totalDegree (p := p) n width ℓ polys S
      · intro x
        dsimp
        intro hbits
        let y : Fin n → ZMod p := fun j ↦ ((x j : Nat) : ZMod p)
        have htarget :
            (∏ i, (1 - (1 - MvPolynomial.eval y (polys i)) ^ (p - 1)) : ZMod p) =
              ((∏ i, bitify (p := p) (MvPolynomial.eval y (polys i)) : Fin 2) : Nat) := by
          exact exactAnd_on_bits (p := p)
            (fun i ↦ MvPolynomial.eval y (polys i))
            (by intro i; simpa [y] using hbits i)
        have hbad := approxAnd_pointwise_bad_count (p := p) n width ℓ polys y
        have hfilter :
            (Finset.univ.filter (fun s : Fin ℓ → Finset (Fin width) =>
              (approxAnd p polys s).eval y ≠
                ((∏ i, bitify (p := p) (MvPolynomial.eval y (polys i)) : Fin 2) : Nat))) =
            (Finset.univ.filter (fun s : Fin ℓ → Finset (Fin width) =>
              (approxAnd p polys s).eval y ≠
                ∏ i, (1 - (1 - MvPolynomial.eval y (polys i)) ^ (p - 1)))) := by
          ext s
          simp [← htarget]
        rw [hfilter]
        calc
          (Finset.univ.filter (fun s : Fin ℓ → Finset (Fin width) =>
            (approxAnd p polys s).eval y ≠
              ∏ i, (1 - (1 - MvPolynomial.eval y (polys i)) ^ (p - 1)))).card * 2 ^ ℓ
              ≤ 2 ^ (width * ℓ) := by
                simpa [y] using hbad
          _ = Fintype.card (Fin ℓ → Finset (Fin width)) :=
              (approxSeed_card width ℓ).symm
    · rcases hMod with ⟨width, rfl⟩
      refine ⟨PUnit, inferInstance, inferInstance, (fun _ => exactMod p polys), ?_, ?_, ?_⟩
      · simp
      · intro s
        refine le_trans (exactMod_totalDegree (p := p) n width polys) ?_
        have hsupmul : (⨆ i, (polys i).totalDegree) ≤ ℓ * (⨆ i, (polys i).totalDegree) := by
          simpa [one_mul] using Nat.mul_le_mul_right (⨆ i, (polys i).totalDegree) hℓ1
        have hmul' :
            (p - 1) * (⨆ i, (polys i).totalDegree) ≤
              (p - 1) * (ℓ * (⨆ i, (polys i).totalDegree)) := by
          exact Nat.mul_le_mul_left (p - 1) hsupmul
        simpa [mul_assoc] using hmul'
      · intro x
        dsimp
        intro hbits
        have hcorrect :
            (exactMod p polys).eval (fun j ↦ ((x j : Nat) : ZMod p)) =
              ((modGateOp p width).func
                (fun i ↦ bitify (p := p)
                  ((polys i).eval (fun j ↦ ((x j : Nat) : ZMod p)))) : Nat) := by
          simpa [exactMod] using exactMod_on_bits (p := p)
            (fun i ↦ MvPolynomial.eval (fun j ↦ ((x j : Nat) : ZMod p)) (polys i)) hbits
        have hfilter :
            (Finset.univ.filter (fun s : PUnit =>
              (exactMod p polys).eval (fun j ↦ ((x j : Nat) : ZMod p)) ≠
                ((modGateOp p width).func
                  (fun i ↦ bitify (p := p)
                    ((polys i).eval (fun j ↦ ((x j : Nat) : ZMod p)))) : Nat))) = ∅ := by
          ext s
          constructor
          · intro hs
            exact False.elim ((Finset.mem_filter.mp hs).2 hcorrect)
          · intro hs
            exact False.elim (by simp at hs)
        rw [hfilter]
        simp


end ACP
