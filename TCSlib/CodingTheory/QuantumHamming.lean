/-
Quantum Hamming bound for stabilizer codes.
This module follows a similar structure to the classical hamming_bound in Basic.lean.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual
import Mathlib.Data.Prod.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Order.Disjoint
import Mathlib.Tactic.Linarith

import TCSlib.CodingTheory.Basic
import TCSlib.CodingTheory.CSS

open Finset Set

namespace CodingTheory

variable {α : Type*} [Field α] [Fintype α] [DecidableEq α]
variable {n : ℕ}

/-! 1) Quantum code dimension -/

-- The dimension of a quantum code is: k = n - (stabilizer rank)
-- For a [[n,k,d]] stabilizer code where the stabilizer has rank r, we have k = n - r
noncomputable def quantum_code_dimension (S : Submodule α (SympVec n α))
  [FiniteDimensional α (SympVec n α)] : ℕ :=
  n - FiniteDimensional.finrank α S

/-! 2) Pauli error balls -/

-- Error ball: set of all Pauli errors with weight ≤ t
noncomputable def pauli_error_ball (t : ℕ) (p : SympVec n α) : Finset (SympVec n α) :=
  {p' : SympVec n α | pauliWeight (p' - p) ≤ t}.toFinset

-- Size of a Pauli error ball (independent of center for translation-invariant metric)
noncomputable def pauli_error_ball_size (t : ℕ) : ℕ :=
  -- For q-ary code: |B_t| = ∑_{i=0}^t (n choose i) * (q^2 - 1)^i
  -- For each of the i positions, we choose a non-zero vector in α × α.
  by
    classical
    exact Finset.sum (Finset.range (t + 1)) (fun i =>
      Nat.choose n i * ((Fintype.card α)^2 - 1)^i)

-- The size is independent of the center
lemma pauli_error_ball_size_independent (t : ℕ) (p q : SympVec n α) :
  (pauli_error_ball t p).card = (pauli_error_ball t q).card := by
  -- Translation invariance: error balls have same size regardless of center
  -- Use bijection: map p' ↦ p' + (q - p) to translate error ball at p to error ball at q
  classical
  let f : SympVec n α → SympVec n α := fun p' => p' + (q - p)
  have h_inj : Function.Injective f := by
    intro x y hxy
    simp [f] at hxy
    have : (x + (q - p)) - (q - p) = (y + (q - p)) - (q - p) := by rw [hxy]
    simp [sub_add_cancel] at this
    exact this
  have h_ball_eq : (pauli_error_ball t p).image f = pauli_error_ball t q := by
    ext r
    simp [pauli_error_ball, f]
    constructor
    · intro ⟨p', hp', hpr⟩
      rw [← hpr]
      simp [pauli_error_ball]
      have : (p' + (q - p)) - q = p' - p := by
        ext <;> simp [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, add_sub_assoc, sub_add_eq_sub_sub]
      rw [this]
      exact hp'
    · intro hr
      use r - (q - p)
      constructor
      · simp [pauli_error_ball]
        have : (r - (q - p)) - p = r - q := by
          ext <;> simp [Prod.fst_sub, Prod.snd_sub, sub_sub, add_comm]
        rw [this]
        exact hr
      · simp [f]
        ext <;> simp [Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub, sub_add_cancel]
  rw [← h_ball_eq, Finset.card_image_of_injective _ h_inj]

lemma pauli_error_ball_card (t : ℕ) (p : SympVec n α) :
  (pauli_error_ball t p).card = pauli_error_ball_size t := by
  classical
  let zero_vec : SympVec n α := ((fun _ => 0), (fun _ => 0))
  have h_trans : (pauli_error_ball t p).card = (pauli_error_ball t zero_vec).card :=
    pauli_error_ball_size_independent t p zero_vec
  rw [h_trans]
  simp [pauli_error_ball, pauli_error_ball_size, zero_vec]
  rw [Set.toFinset_card]
  have h_union : {p' : SympVec n α | pauliWeight p' ≤ t} =
    ⋃ i ∈ Finset.range (t + 1), {p' : SympVec n α | pauliWeight p' = i} := by
    ext p'
    simp
    constructor
    · intro h
      use pauliWeight p'
      simp [h]
    · intro h
      rcases h with ⟨i, hi, h_eq⟩
      rw [← h_eq]
      exact Finset.mem_range.1 hi
  rw [h_union]
  have h_disj : ∀ i j, i ≠ j → Disjoint {p' : SympVec n α | pauliWeight p' = i}
    {p' : SympVec n α | pauliWeight p' = j} := by
    intros i j hij
    simp [Set.disjoint_iff]
    intro p' h1 h2
    rw [Set.mem_setOf] at h1 h2
    linarith
  have h_union_card : (⋃ i ∈ Finset.range (t + 1), {p' : SympVec n α | pauliWeight p' = i}).toFinset.card =
    Finset.sum (Finset.range (t + 1)) (fun i => ({p' : SympVec n α | pauliWeight p' = i}.toFinset.card)) := by
    rw [Set.toFinset_card]
    have h_partition : ⋃ i ∈ Finset.range (t + 1), {p' : SympVec n α | pauliWeight p' = i} =
      {p' : SympVec n α | pauliWeight p' ≤ t} := by
      ext p'
      simp
      constructor
      · intro h
        rcases h with ⟨i, hi, h_eq⟩
        rw [← h_eq]
        exact Finset.mem_range.1 hi
      · intro h
        use pauliWeight p'
        simp [h]
    rw [h_partition]
    have h_sum : Finset.sum (Finset.range (t + 1)) (fun i => ({p' : SympVec n α | pauliWeight p' = i}.toFinset.card)) =
      (⋃ i ∈ Finset.range (t + 1), {p' : SympVec n α | pauliWeight p' = i}).toFinset.card := by
      classical
      have h_disj_fin : ∀ i j, i ≠ j →
        Disjoint ({p' : SympVec n α | pauliWeight p' = i}.toFinset)
        ({p' : SympVec n α | pauliWeight p' = j}.toFinset) := by
        intros i j hij
        simp [Finset.disjoint_iff_ne]
        intro p1 hp1 p2 hp2 h_eq
        simp at hp1 hp2
        linarith
      have h_union_eq : (⋃ i ∈ Finset.range (t + 1), {p' : SympVec n α | pauliWeight p' = i}).toFinset =
        (Finset.range (t + 1)).biUnion (fun i => {p' : SympVec n α | pauliWeight p' = i}.toFinset) := by
        ext p'
        simp
        constructor
        · intro h
          rcases h with ⟨i, hi, h_mem⟩
          use i
          simp [hi, h_mem]
        · intro h
          obtain ⟨i, hi, h_mem⟩ := h
          use i
          simp [hi, h_mem]
      rw [h_union_eq, Finset.card_biUnion h_disj_fin]
    rw [← h_sum]
  rw [h_union_card]
  apply Finset.sum_congr rfl
  intro i hi
  have h_count : ({p' : SympVec n α | pauliWeight p' = i}.toFinset.card) =
    Nat.choose n i * ((Fintype.card α)^2 - 1)^i := by
    let pos_comb : Finset (Finset (Fin n)) := Finset.powersetCard i Finset.univ
    have h_pos_card : pos_comb.card = Nat.choose n i := by simp [pos_comb, Finset.card_powersetCard]
    let nonzero_vecs := {v : α × α | v ≠ (0, 0)}.toFinset
    have h_nonzero_vecs_card : nonzero_vecs.card = (Fintype.card α)^2 - 1 := by
      rw [Set.toFinset_card]
      simp [nonzero_vecs]
      rw [Fintype.card_prod]
      rfl
    let S := pos_comb.sigma (fun s => (s → nonzero_vecs))
    have h_card_S : S.card = Nat.choose n i * ((Fintype.card α)^2 - 1)^i := by
      simp [S]
      rw [Finset.card_sigma]
      apply Finset.sum_eq_card_nsmul
      intro s hs
      simp
      rw [Fintype.card_pi]
      rw [h_nonzero_vecs_card]
      rw [Finset.card_powersetCard] at hs
      simp [hs]
    have h_bij : S.card = ({p' : SympVec n α | pauliWeight p' = i}.toFinset.card) := by
      let f : (s : Finset (Fin n)) × (s → nonzero_vecs) → SympVec n α := fun ⟨s, vals⟩ =>
        (fun j => if h : j ∈ s then (vals ⟨j, h⟩).val.1 else 0,
         fun j => if h : j ∈ s then (vals ⟨j, h⟩).val.2 else 0)
      apply Finset.card_bij (fun x hx => f x)
      · intro ⟨s, vals⟩ hs
        simp [pauliWeight, f]
        have h_supp : (Finset.univ.filter (fun j =>
            (if h : j ∈ s then (vals ⟨j, h⟩).val.1 else 0) ≠ 0 ∨
            (if h : j ∈ s then (vals ⟨j, h⟩).val.2 else 0) ≠ 0)) = s := by
          ext j
          simp
          constructor
          · intro h
            by_contra h_notin
            simp [h_notin] at h
            tauto
          · intro h_in
            simp [h_in]
            have : (vals ⟨j, h_in⟩).val ≠ (0, 0) := (vals ⟨j, h_in⟩).property
            simp [Prod.ext_iff] at this
            exact this
        rw [h_supp]
        exact (Finset.mem_powersetCard.mp (by simp [S] at hs; exact hs.1)).2
      · intro ⟨s1, vals1⟩ ⟨s2, vals2⟩ hs1 hs2 h_eq
        simp [f] at h_eq
        have h_s : s1 = s2 := by
          ext j
          constructor
          · intro h1
            have : (f ⟨s1, vals1⟩).1 j ≠ 0 ∨ (f ⟨s1, vals1⟩).2 j ≠ 0 := by
               simp [f, h1]
               have := (vals1 ⟨j, h1⟩).property
               simp [Prod.ext_iff] at this
               exact this
            rw [h_eq.1, h_eq.2] at this
            simp [f] at this
            by_contra h2
            simp [h2] at this
            tauto
          · intro h2
            have : (f ⟨s2, vals2⟩).1 j ≠ 0 ∨ (f ⟨s2, vals2⟩).2 j ≠ 0 := by
               simp [f, h2]
               have := (vals2 ⟨j, h2⟩).property
               simp [Prod.ext_iff] at this
               exact this
            rw [←h_eq.1, ←h_eq.2] at this
            simp [f] at this
            by_contra h1
            simp [h1] at this
            tauto
        subst h_s
        congr
        funext ⟨j, hj⟩
        apply Subtype.ext
        apply Prod.ext
        · have := congr_fun h_eq.1 j
          simp [f, hj] at this
          exact this
        · have := congr_fun h_eq.2 j
          simp [f, hj] at this
          exact this
      · intro p hp
        simp at hp
        let s := Finset.univ.filter (fun j => p.1 j ≠ 0 ∨ p.2 j ≠ 0)
        have h_card : s.card = i := hp
        have h_s_in : s ∈ pos_comb := by
          simp [pos_comb, Finset.mem_powersetCard, h_card]
        let vals (x : s) : nonzero_vecs :=
          ⟨(p.1 x, p.2 x), by
            intro h0
            simp [Prod.ext_iff] at h0
            have : x.1 ∈ s := x.2
            simp [s] at this
            tauto⟩
        use ⟨s, vals⟩
        constructor
        · simp [S, h_s_in]
        · simp [f]
          ext j
          · simp
            by_cases h : j ∈ s
            · simp [h]
            · simp [s] at h
              push_neg at h
              exact h.1.symm
          · simp
            by_cases h : j ∈ s
            · simp [h]
            · simp [s] at h
              push_neg at h
              exact h.2.symm
    rw [← h_bij, h_card_S]
  exact h_count

/-! 3) Quantum distance -/

noncomputable def quantum_distance (S : Stabilizer n α) : ℕ :=
  by
    classical
    let universe : Finset (SympVec n α) := Finset.univ
    let candidates := universe.filter (fun p =>
      (∀ s ∈ S.S.toSet, symplecticForm p s = 0) ∧ ¬ p ∈ S.S ∧ pauliWeight p ≠ 0)
    exact if h : candidates.Nonempty then
      let ws := candidates.image pauliWeight
      have hw : ws.Nonempty := by
        rcases h with ⟨x, hx⟩
        exact ⟨_, Finset.mem_image.mpr ⟨x, hx, rfl⟩⟩
      Finset.min' ws hw
    else 0

lemma quantum_distance_le_pauliWeight {S : Stabilizer n α} (p : SympVec n α)
    (h_comm : ∀ s ∈ S.S.toSet, symplecticForm p s = 0)
    (hp_notin : p ∉ S.S) (hp_weight : pauliWeight p ≠ 0) :
    quantum_distance (n:=n) S ≤ pauliWeight p := by
  classical
  let universe : Finset (SympVec n α) := Finset.univ
  let candidates := universe.filter (fun p =>
      (∀ s ∈ S.S.toSet, symplecticForm p s = 0) ∧ ¬ p ∈ S.S ∧ pauliWeight p ≠ 0)
  have h_mem : p ∈ candidates := by
    simp [candidates, universe, h_comm, hp_notin, hp_weight]
  have h_nonempty : candidates.Nonempty := ⟨p, h_mem⟩
  have h_img_nonempty :
      (candidates.image pauliWeight).Nonempty :=
    ⟨pauliWeight p, Finset.mem_image.mpr ⟨p, h_mem, rfl⟩⟩
  have h_qdist :
      quantum_distance (n:=n) S
        = Finset.min' (candidates.image pauliWeight) h_img_nonempty := by
    simp [quantum_distance, candidates, universe, h_nonempty, h_img_nonempty]
  have h_mem_img :
      pauliWeight p ∈ candidates.image pauliWeight :=
    Finset.mem_image.mpr ⟨p, h_mem, rfl⟩
  have h_min_le :
      Finset.min' (candidates.image pauliWeight) h_img_nonempty
        ≤ pauliWeight p :=
    Finset.min'_le _ _ _ h_mem_img
  exact h_qdist.trans_le h_min_le

/-- Evaluate the symplectic form after subtracting on the left. -/
lemma symplecticForm_sub_left (u v w : SympVec n α) :
    symplecticForm (n:=n) (u - v) w
      = symplecticForm (n:=n) u w - symplecticForm (n:=n) v w := by
  classical
  simp [symplecticForm, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, add_mul,
    mul_add, Finset.sum_sub_distrib]

/-- If both elements commute with the stabilizer, so does their difference. -/
lemma commutesWithStabilizer_sub {S : Stabilizer n α} {p q : SympVec n α}
    (hp : ∀ s ∈ S.S.toSet, symplecticForm (n:=n) p s = 0)
    (hq : ∀ s ∈ S.S.toSet, symplecticForm (n:=n) q s = 0) :
    ∀ s ∈ S.S.toSet, symplecticForm (n:=n) (p - q) s = 0 := by
  intro s hs
  have hp' := hp s hs
  have hq' := hq s hs
  simp [symplecticForm_sub_left, hp', hq']

/-- If `p` and `q` commute with the stabilizer and represent different logical
operators (so their difference is not in the stabilizer), then the quantum distance
is bounded above by the weight of their difference. -/
lemma quantum_distance_le_weight_sub {S : Stabilizer n α} {p q : SympVec n α}
    (hp : ∀ s ∈ S.S.toSet, symplecticForm (n:=n) p s = 0)
    (hq : ∀ s ∈ S.S.toSet, symplecticForm (n:=n) q s = 0)
    (h_notin : p - q ∉ S.S) (h_weight : pauliWeight (p - q) ≠ 0) :
    quantum_distance (n:=n) S ≤ pauliWeight (p - q) := by
  have h_comm := commutesWithStabilizer_sub (S:=S) hp hq
  simpa using
    quantum_distance_le_pauliWeight (S:=S) (p:=p - q) h_comm h_notin h_weight

/-- A convenient inequality version phrased with an explicit distance parameter. -/
lemma pauliWeight_sub_ge_of_commuting {S : Stabilizer n α} {p q : SympVec n α}
    (hp : ∀ s ∈ S.S.toSet, symplecticForm (n:=n) p s = 0)
    (hq : ∀ s ∈ S.S.toSet, symplecticForm (n:=n) q s = 0)
    (h_notin : p - q ∉ S.S) (h_weight : pauliWeight (p - q) ≠ 0)
    {d : ℕ} (hd : d ≤ quantum_distance (n:=n) S) :
    d ≤ pauliWeight (p - q) := by
  have h_qdist := quantum_distance_le_weight_sub (S:=S) hp hq h_notin h_weight
  exact hd.trans h_qdist

/-! 4) Disjointness of error balls -/

lemma pauli_error_ball_disjoint {S : Stabilizer n α} (d : ℕ) (hd : 0 < d)
  (p₁ p₂ : SympVec n α) (hp₁ : p₁ ∈ S.S) (hp₂ : p₂ ∈ S.S) (hp_ne : p₁ ≠ p₂)
  (h_weight : pauliWeight (p₁ - p₂) ≥ d) :
  Disjoint (pauli_error_ball (Nat.floor (((d : ℝ) - 1) / 2)) p₁)
           (pauli_error_ball (Nat.floor (((d : ℝ) - 1) / 2)) p₂) := by
  classical
  simp [Finset.disjoint_iff_ne]
  intro x hx y hy hxy
  have hx_ball : pauliWeight (x - p₁) ≤ Nat.floor (((d : ℝ) - 1) / 2) := by
    simp [pauli_error_ball] at hx
    exact hx
  have hy_ball : pauliWeight (y - p₂) ≤ Nat.floor (((d : ℝ) - 1) / 2) := by
    simp [pauli_error_ball] at hy
    exact hy
  have h_eq : x = y := hxy
  rw [h_eq] at hy_ball
  have h_weight : pauliWeight (x - p₁) + pauliWeight (x - p₂) ≤
    Nat.floor (((d : ℝ) - 1) / 2) + Nat.floor (((d : ℝ) - 1) / 2) := by
    linarith
  have h_triangle : pauliWeight (p₁ - p₂) ≤ pauliWeight (x - p₁) + pauliWeight (x - p₂) := by
    simp [pauliWeight]
    have h_sub : (p₁ - p₂).1 = (x - p₁).1 + (x - p₂).1 ∧ (p₁ - p₂).2 = (x - p₁).2 + (x - p₂).2 := by
      constructor <;> ext i <;> simp [Prod.fst_sub, Prod.snd_sub, sub_add]
    have h_union : {i | (p₁ - p₂).1 i ≠ 0 ∨ (p₁ - p₂).2 i ≠ 0} ⊆
      {i | (x - p₁).1 i ≠ 0 ∨ (x - p₁).2 i ≠ 0} ∪ {i | (x - p₂).1 i ≠ 0 ∨ (x - p₂).2 i ≠ 0} := by
      intro i hi
      simp at hi
      rw [h_sub.1, h_sub.2] at hi
      by_cases h1 : (x - p₁).1 i ≠ 0 ∨ (x - p₁).2 i ≠ 0
      · left; exact h1
      · right
        push_neg at h1
        have : (x - p₂).1 i ≠ 0 ∨ (x - p₂).2 i ≠ 0 := by
          by_contra h
          push_neg at h
          have : (p₁ - p₂).1 i = 0 := by simp [h_sub.1, h1.1, h.1]
          have : (p₁ - p₂).2 i = 0 := by simp [h_sub.2, h1.2, h.2]
          tauto
        exact this
    have h_card : (Finset.univ.filter (fun i => (p₁ - p₂).1 i ≠ 0 ∨ (p₁ - p₂).2 i ≠ 0)).card ≤
      (Finset.univ.filter (fun i => (x - p₁).1 i ≠ 0 ∨ (x - p₁).2 i ≠ 0)).card +
      (Finset.univ.filter (fun i => (x - p₂).1 i ≠ 0 ∨ (x - p₂).2 i ≠ 0)).card := by
      have h1 : Finset.univ.filter (fun i => (p₁ - p₂).1 i ≠ 0 ∨ (p₁ - p₂).2 i ≠ 0) ⊆
        (Finset.univ.filter (fun i => (x - p₁).1 i ≠ 0 ∨ (x - p₁).2 i ≠ 0)) ∪
        (Finset.univ.filter (fun i => (x - p₂).1 i ≠ 0 ∨ (x - p₂).2 i ≠ 0)) := by
        intro i hi
        simp at hi
        rw [Finset.mem_union]
        rw [← Set.mem_setOf] at hi
        rcases h_union hi with (h | h)
        · left; simp; exact h
        · right; simp; exact h
      have h2 := Finset.card_le_card h1
      have h3 : ((Finset.univ.filter (fun i => (x - p₁).1 i ≠ 0 ∨ (x - p₁).2 i ≠ 0)) ∪
        (Finset.univ.filter (fun i => (x - p₂).1 i ≠ 0 ∨ (x - p₂).2 i ≠ 0))).card ≤
        (Finset.univ.filter (fun i => (x - p₁).1 i ≠ 0 ∨ (x - p₁).2 i ≠ 0)).card +
        (Finset.univ.filter (fun i => (x - p₂).1 i ≠ 0 ∨ (x - p₂).2 i ≠ 0)).card := by
        apply Finset.card_union_le
      linarith
    exact h_card
  have h_floor : Nat.floor (((d : ℝ) - 1) / 2) + Nat.floor (((d : ℝ) - 1) / 2) < d := by
    have h1 : ((d : ℝ) - 1) / 2 < d / 2 := by linarith
    have h2 : Nat.floor (((d : ℝ) - 1) / 2) < d / 2 := by
      apply Nat.floor_lt
      linarith
    linarith
  linarith [h_weight, h_triangle, h_weight, h_floor]

/-! 4) Quantum Hamming bound -/

-- Quantum Hamming bound: for a [[n,k,d]] stabilizer code,
-- 2^k ≤ 2^n / (sum of error ball sizes)
-- Or equivalently: 2^k * (sum of error ball sizes) ≤ 2^n
-- For q-ary codes: q^k ≤ q^n / (sum of error ball sizes)
-- Or: q^k * (sum of error ball sizes) ≤ q^n

-- Helper for triangle inequality on Pauli weight
lemma pauliWeight_triangle (p q : SympVec n α) :
  pauliWeight (p - q) ≤ pauliWeight p + pauliWeight q := by
  simp [pauliWeight]
  have h_sub : ∀ i, (p - q).1 i = p.1 i - q.1 i ∧ (p - q).2 i = p.2 i - q.2 i := by
    intro i; simp [Prod.fst_sub, Prod.snd_sub, sub_eq_add_neg]
  apply Finset.card_le_card_of_inj_on (f := id)
  · intro i hi
    simp at hi
    simp
    by_contra h_not
    push_neg at h_not
    simp [h_sub] at hi
    have : p.1 i = 0 ∧ p.2 i = 0 := h_not.1
    have : q.1 i = 0 ∧ q.2 i = 0 := h_not.2
    simp [this] at hi
  · intro _ _ _ _ h; exact h

theorem quantum_hamming_bound (n k d : ℕ) (S : Stabilizer n α)
  [FiniteDimensional α (SympVec n α)]
  (h_dim : k = quantum_code_dimension S.S)
  (h_dist : 0 < d)
  (h_d_le_n : d ≤ n)
  (h_dist_bound : d ≤ quantum_distance S) -- Distance matches the code's capability
  (h_q : Fintype.card α > 1)
  -- Assumption required for the bound to hold on raw error counts (non-degenerate code):
  (h_pure : ∀ e ∈ S.S, pauliWeight e < d → e = 0) :
  (Fintype.card α)^k *
    (Finset.sum (Finset.range ((Nat.floor (((d : ℝ) - 1) / 2)) + 1))
      (fun i => Nat.choose n i * ((Fintype.card α)^2 - 1)^i))
  ≤ (Fintype.card α)^n := by
  classical
  let t := Nat.floor (((d : ℝ) - 1) / 2)
  let ball := pauli_error_ball t 0

  -- 1. Cardinality of the ball
  have h_ball_card : ball.card = Finset.sum (Finset.range (t + 1))
      (fun i => Nat.choose n i * ((Fintype.card α)^2 - 1)^i) := by
    rw [pauli_error_ball_card]
    rw [pauli_error_ball_size]

  -- 2. Syndrome map
  let syndrome_map : SympVec n α →ₗ[α] (S.S →ₗ[α] α) := {
    toFun := fun p => {
      toFun := fun s => symplecticForm p s.val
      map_add' := fun x y => by simp [symplecticForm]; ring
      map_smul' := fun c x => by simp [symplecticForm]; ring
    }
    map_add' := fun x y => by ext s; simp [symplecticForm]; ring
    map_smul' := fun c x => by ext s; simp [symplecticForm]; ring
  }
  let syndrome_space := S.S →ₗ[α] α

  -- 3. Bound the cardinality of the syndrome space
  have h_syndrome_space_dim : FiniteDimensional.finrank α syndrome_space = n - k := by
    rw [LinearMap.finrank_dual_eq_finrank]
    simp [quantum_code_dimension] at h_dim
    have h_rank : FiniteDimensional.finrank α S.S = n - k := by linarith
    exact h_rank

  have h_syndrome_card : Fintype.card syndrome_space = (Fintype.card α)^(n - k) := by
    let b := FiniteDimensional.finBasis α syndrome_space
    rw [FiniteDimensional.finrank_eq_card_basis b] at h_syndrome_space_dim
    rw [Fintype.card_eq.mpr ⟨b.equivFun⟩, Fintype.card_fun, Fintype.card_fin]
    rw [← h_syndrome_space_dim]

  -- 4. Injectivity on the ball
  have h_inj : Set.InjOn syndrome_map ball := by
    intro x hx y hy h_eq
    simp [ball, pauli_error_ball] at hx hy
    -- s(x)=s(y) => x-y in S^perp
    have h_diff_perp : ∀ s ∈ S.S, symplecticForm (x - y) s = 0 := by
      intro s hs
      have : (syndrome_map x) ⟨s, hs⟩ = (syndrome_map y) ⟨s, hs⟩ := by rw [h_eq]
      simp [syndrome_map] at this
      exact this

    have h_weight : pauliWeight (x - y) < d := by
      calc
        pauliWeight (x - y) ≤ pauliWeight x + pauliWeight y := pauliWeight_triangle x y
        _ ≤ t + t := add_le_add hx hy
        _ = 2 * Nat.floor (((d : ℝ) - 1) / 2) := by ring
        _ ≤ 2 * (((d : ℝ) - 1) / 2) := by
             apply mul_le_mul_of_nonneg_left
             apply Nat.floor_le
             apply div_nonneg
             simp; exact le_of_lt h_dist; simp
             simp
        _ = (d : ℝ) - 1 := by field_simp
        _ < d := by linarith

    -- x-y in S^perp. If x-y not in S, then wt >= d (by quantum distance).
    -- But wt < d. So x-y in S.
    have h_in_S : x - y ∈ S.S := by
       by_contra h_notin
       have h_dist_def : quantum_distance S ≤ pauliWeight (x - y) := by
         apply quantum_distance_le_pauliWeight
         · intro s hs; exact h_diff_perp s hs
         · exact h_notin
         · intro h0; rw [h0] at h_weight; simp [h_dist] at h_weight
       linarith

    have : x - y = 0 := h_pure (x - y) h_in_S h_weight
    exact sub_eq_zero.mp this

  -- 5. Map cardinality
  have h_map_card : ball.card ≤ syndrome_space.card := by
    -- The image of the ball is a subset of the syndrome space
    let ball_image := ball.image syndrome_map
    have : ball.card = ball_image.card := by
      symm
      apply Finset.card_image_of_inj_on
      exact h_inj
    rw [this]
    apply Finset.card_le_univ

  rw [h_ball_card, h_syndrome_card] at h_map_card

  -- 6. Conclusion
  calc
    (Fintype.card α)^k * (Finset.sum (Finset.range (t + 1)) (fun i => Nat.choose n i * ((Fintype.card α)^2 - 1)^i))
    ≤ (Fintype.card α)^k * (Fintype.card α)^(n - k) := Nat.mul_le_mul_left _ h_map_card
    _ = (Fintype.card α)^(k + (n - k)) := by rw [← pow_add]
    _ = (Fintype.card α)^n := by
        congr
        simp [quantum_code_dimension] at h_dim
        have : k + (n - k) = k + FiniteDimensional.finrank α S.S := by
           have : n - k = FiniteDimensional.finrank α S.S := by linarith
           rw [this]
        rw [this]
        linarith
        have h_iso_dim : FiniteDimensional.finrank α S.S ≤ n := by
           have h_nondeg : ∀ u, (∀ v, symplecticForm (n:=n) u v = 0) → u = 0 := by
             intro u hu
             ext i
             · let v : SympVec n α := ((fun _ => 0), (fun k => if k = i then 1 else 0))
               have hv := hu v
               simp [symplecticForm] at hv
               rw [Finset.sum_eq_single i] at hv
               · simp at hv
                 exact hv
               · intro b _ hb
                 simp [v]
                 have : b ≠ i := hb
                 simp [this]
               · intro hi
                 exact (hi (Finset.mem_univ i)).elim
             · let v : SympVec n α := ((fun k => if k = i then 1 else 0), (fun _ => 0))
               have hv := hu v
               simp [symplecticForm] at hv
               rw [Finset.sum_eq_single i] at hv
               · simp at hv
                 exact neg_eq_zero.mp hv
               · intro b _ hb
                 simp [v]
                 have : b ≠ i := hb
                 simp [this]
               · intro hi
                 exact (hi (Finset.mem_univ i)).elim

           let B := symplecticForm (n:=n)
           have h_sub : S.S ≤ Submodule.dualOrthogonal B S.S := by
             intro u hu v hv
             exact S.isIso u hu v hv

           let S_perp : Submodule α (SympVec n α) :=
             { carrier := {v | ∀ u ∈ S.S, symplecticForm (n:=n) u v = 0}
               add_mem' := by
                 intros a b ha hb u hu
                 simp [symplecticForm, ha u hu, hb u hu]
                 repeat rw [mul_add, mul_add, Finset.sum_add_distrib]; ring
               smul_mem' := by
                 intros c x hx u hu
                 simp [symplecticForm]
                 rw [hx u hu]
                 ring
                 simp [symplecticForm, mul_sum]
                 apply Finset.sum_congr rfl
                 intro i _
                 ring
               zero_mem' := by
                 intro u hu
                 simp [symplecticForm]
             }

           have h_dim_add : FiniteDimensional.finrank α S.S + FiniteDimensional.finrank α S_perp = 2 * n := by
             let to_dual : SympVec n α →ₗ[α] Module.Dual α (SympVec n α) :=
               LinearMap.mk₂ α symplecticForm (by intros; simp [symplecticForm]; ring) (by intros; simp [symplecticForm]; ring) (by intros; simp [symplecticForm]; ring) (by intros; simp [symplecticForm]; ring)

             have h_ker : LinearMap.ker to_dual = ⊥ := by
               ext x
               simp [LinearMap.ker, to_dual]
               constructor
               · intro h
                 apply h_nondeg x
                 intro v
                 have := LinearMap.congr_fun h v
                 exact this
               · intro h; simp [h]

             have h_iso : FiniteDimensional.finrank α S_perp = FiniteDimensional.finrank α (S.S.dualAnnihilator) := by
               rw [LinearMap.finrank_map_of_injective]
               apply Submodule.finrank_comap_eq_of_surjective
               rw [← LinearMap.range_eq_top]
               apply LinearMap.range_eq_top_of_injective
               exact h_ker

             rw [h_iso]
             rw [Submodule.finrank_dualAnnihilator_eq]
             have h_total : FiniteDimensional.finrank α (SympVec n α) = 2 * n := by
               simp [SympVec]
               rw [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fun]
               simp
             rw [h_total]

           have h_le : FiniteDimensional.finrank α S.S ≤ FiniteDimensional.finrank α S_perp := by
             apply Submodule.finrank_mono
             exact h_sub

           linarith
        linarith

end CodingTheory
