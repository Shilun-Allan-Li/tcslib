import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Linarith
import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic

import TCSlib.CodingTheory.QuantumHamming

open Finset
open scoped BigOperators

namespace CodingTheory

variable {α : Type*} [Field α] [Fintype α] [DecidableEq α]
variable {n : ℕ}

/-! ## Symplectic Form Bilinearity -/

noncomputable def symplecticBilin : LinearMap.BilinForm α (SympVec n α) :=
  LinearMap.mk₂ α symplecticForm
    (by intro x y z; simp only [symplecticForm, Prod.fst_add, Prod.snd_add, Pi.add_apply]
        rw [← Finset.sum_add_distrib]; congr 1; ext i; ring)
    (by intro c x y; simp only [symplecticForm, Prod.fst_smul, Prod.snd_smul, Pi.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum]; congr 1; ext i; ring)
    (by intro x y z; simp only [symplecticForm, Prod.fst_add, Prod.snd_add, Pi.add_apply]
        rw [← Finset.sum_add_distrib]; congr 1; ext i; ring)
    (by intro c x y; simp only [symplecticForm, Prod.fst_smul, Prod.snd_smul, Pi.smul_apply, smul_eq_mul]
        rw [← Finset.mul_sum]; congr 1; ext i; ring)

lemma symplecticForm_add_left (x y z : SympVec n α) :
    symplecticForm (x + y) z = symplecticForm x z + symplecticForm y z := by
  simp only [symplecticForm, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]; congr 1; ext i; ring

lemma symplecticForm_add_right (x y z : SympVec n α) :
    symplecticForm x (y + z) = symplecticForm x y + symplecticForm x z := by
  simp only [symplecticForm, Prod.fst_add, Prod.snd_add, Pi.add_apply]
  rw [← Finset.sum_add_distrib]; congr 1; ext i; ring

lemma symplecticForm_smul_left (c : α) (x y : SympVec n α) :
    symplecticForm (c • x) y = c * symplecticForm x y := by
  simp only [symplecticForm, Prod.fst_smul, Prod.snd_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]; congr 1; ext i; ring

lemma symplecticForm_smul_right (c : α) (x y : SympVec n α) :
    symplecticForm x (c • y) = c * symplecticForm x y := by
  simp only [symplecticForm, Prod.fst_smul, Prod.snd_smul, Pi.smul_apply, smul_eq_mul]
  rw [← Finset.mul_sum]; congr 1; ext i; ring

lemma symplecticForm_sum_left {ι : Type*} (s : Finset ι) (f : ι → SympVec n α) (y : SympVec n α) :
    symplecticForm (∑ i ∈ s, f i) y = ∑ i ∈ s, symplecticForm (f i) y := by
  induction s using Finset.induction_on with
  | empty => simp [symplecticForm]
  | insert ha ih => rw [Finset.sum_insert ha, symplecticForm_add_left, ih, Finset.sum_insert ha]

lemma symplecticForm_sum_right {ι : Type*} (s : Finset ι) (x : SympVec n α) (f : ι → SympVec n α) :
    symplecticForm x (∑ i ∈ s, f i) = ∑ i ∈ s, symplecticForm x (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [symplecticForm]
  | insert ha ih => rw [Finset.sum_insert ha, symplecticForm_add_right, ih, Finset.sum_insert ha]

lemma symplecticForm_smul_sum_left {ι : Type*} (s : Finset ι) (l : ι → α) (f : ι → SympVec n α) (y : SympVec n α) :
    symplecticForm (∑ i ∈ s, l i • f i) y = ∑ i ∈ s, l i * symplecticForm (f i) y := by
  rw [symplecticForm_sum_left]; congr 1; ext i; rw [symplecticForm_smul_left]

/-! ## Symplectic Dual -/

def symplecticDual (S : Submodule α (SympVec n α)) : Submodule α (SympVec n α) where
  carrier := {v | ∀ s ∈ S, symplecticForm v s = 0}
  zero_mem' := by intro s _; simp [symplecticForm]
  add_mem' := by
    intro a b ha hb s hs
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [symplecticForm_add_left, ha s hs, hb s hs, add_zero]
  smul_mem' := by
    intro c x hx s hs
    simp only [Set.mem_setOf_eq] at hx ⊢
    rw [symplecticForm_smul_left, hx s hs, mul_zero]

lemma stabilizer_is_isotropic (S : Stabilizer n α) :
    ∀ s ∈ S.S, ∀ t ∈ S.S, symplecticForm s t = 0 := S.isIso

lemma stabilizer_le_symplecticDual (S : Stabilizer n α) : S.S ≤ symplecticDual S.S := by
  intro v hv
  simp only [symplecticDual, Submodule.mem_mk, Set.mem_setOf_eq]
  intro s hs
  exact S.isIso v hv s hs

/-! ## Erasure Correction -/

def ErasureCorrectable (S : Stabilizer n α) (erased : Finset (Fin n)) : Prop :=
  ∀ (p : SympVec n α),
    (∀ i, i ∉ erased → p.1 i = 0 ∧ p.2 i = 0) →
    (∀ s ∈ S.S.toSet, symplecticForm p s = 0) → p ∈ S.S

lemma erasure_correctable_of_dist (S : Stabilizer n α) (erased : Finset (Fin n))
    (h_dist : erased.card < quantum_distance S) : ErasureCorrectable S erased := by
  intro p h_supp h_comm
  by_contra h_notin_S
  have h_weight : pauliWeight p ≤ erased.card := by
    simp [pauliWeight]; apply Finset.card_le_card; intro i hi; simp at hi
    by_contra h_not_in; specialize h_supp i h_not_in; rw [h_supp.1, h_supp.2] at hi; simp at hi
  have h_ne_zero : pauliWeight p ≠ 0 := by
    intro h0
    have : p = 0 := by
      simp [pauliWeight] at h0; ext i
      have h_empty := Finset.eq_empty_of_card_eq_zero h0
      have h1 : p.1 i = 0 := by by_contra h; have : i ∈ {x | p.1 x ≠ 0 ∨ p.2 x ≠ 0} := by simp [h]; rw [h_empty] at this; contradiction
      have h2 : p.2 i = 0 := by by_contra h; have : i ∈ {x | p.1 x ≠ 0 ∨ p.2 x ≠ 0} := by simp [h]; rw [h_empty] at this; contradiction
      simp [h1, h2]
    rw [this] at h_notin_S; exact h_notin_S (Submodule.zero_mem S.S)
  have : quantum_distance S ≤ pauliWeight p := quantum_distance_le_pauliWeight (S:=S) p h_comm h_notin_S h_ne_zero
  linarith

def restrictTo (p : SympVec n α) (erased : Finset (Fin n)) : SympVec n α :=
  (fun i => if i ∈ erased then p.1 i else 0, fun i => if i ∈ erased then p.2 i else 0)

def symplecticFormOn (C : Finset (Fin n)) (p q : SympVec n α) : α :=
  ∑ i ∈ C, (p.1 i * q.2 i - p.2 i * q.1 i)

lemma symplecticFormOn_restrict (erased : Finset (Fin n)) (p q : SympVec n α) :
    symplecticFormOn erased (restrictTo p erased) q = symplecticFormOn erased p q := by
  simp [symplecticFormOn, restrictTo]; congr 1; ext i; split_ifs <;> simp

lemma restrict_logical_to_erased_in_stabilizer (S : Stabilizer n α) (erased : Finset (Fin n))
    (h_corr : ErasureCorrectable S erased) (L : SympVec n α)
    (h_L_comm : ∀ s ∈ S.S.toSet, symplecticForm L s = 0) : restrictTo L erased ∈ S.S := by
  apply h_corr (restrictTo L erased)
  · intro i hi; simp [restrictTo]; split_ifs with h_in; exfalso; exact hi h_in; simp
  · intro s hs
    have h_decomp : symplecticForm (restrictTo L erased) s = symplecticFormOn erased (restrictTo L erased) s + symplecticFormOn (erasedᶜ) (restrictTo L erased) s := by
      classical; simp [symplecticForm, symplecticFormOn]; rw [← Finset.sum_union]
      · congr 1; ext i; simp; tauto
      · simp [Finset.disjoint_iff_ne]; intro x hx hx' h_eq; simp at hx hx'; tauto
    have h_zero_compl : symplecticFormOn (erasedᶜ) (restrictTo L erased) s = 0 := by
      simp [symplecticFormOn, restrictTo]; apply Finset.sum_eq_zero; intro i hi; simp at hi; split_ifs <;> simp
    have h_erased_eq : symplecticFormOn erased (restrictTo L erased) s = symplecticFormOn erased L s := by rw [symplecticFormOn_restrict]
    have h_total : symplecticForm L s = symplecticFormOn erased L s + symplecticFormOn (erasedᶜ) L s := by
      classical; simp [symplecticForm, symplecticFormOn]; rw [← Finset.sum_union]
      · congr 1; ext i; simp; tauto
      · simp [Finset.disjoint_iff_ne]; intro x hx hx' h_eq; simp at hx hx'; tauto
    have h_compl_zero : symplecticFormOn (erasedᶜ) L s = 0 := by rw [← h_total, h_L_comm s hs]; ring
    rw [h_decomp, h_zero_compl, h_erased_eq, ← h_total, h_L_comm s hs, h_compl_zero]; ring

lemma clean_logical_operator (S : Stabilizer n α) (erased : Finset (Fin n))
    (h_corr : ErasureCorrectable S erased) (L : SympVec n α)
    (h_L_comm : ∀ s ∈ S.S.toSet, symplecticForm L s = 0) :
    ∃ s ∈ S.S, ∀ i ∈ erased, (L + s).1 i = 0 ∧ (L + s).2 i = 0 := by
  have h_restrict : restrictTo L erased ∈ S.S := restrict_logical_to_erased_in_stabilizer S erased h_corr L h_L_comm
  use -restrictTo L erased
  constructor
  · exact Submodule.neg_mem S.S h_restrict
  · intro i hi; simp [restrictTo]; split_ifs with h_in; simp [h_in]; exfalso; exact h_in hi

/-! ## Support Submodule -/

def supportSubmodule (C : Finset (Fin n)) : Submodule α (SympVec n α) where
  carrier := {v | ∀ j, j ∉ C → v.1 j = 0 ∧ v.2 j = 0}
  zero_mem' := by simp
  add_mem' := by
    intro v w hv hw j hj; simp only [Set.mem_setOf_eq] at hv hw ⊢
    simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
    constructor; rw [(hv j hj).1, (hw j hj).1]; ring; rw [(hv j hj).2, (hw j hj).2]; ring
  smul_mem' := by
    intro c v hv j hj; simp only [Set.mem_setOf_eq] at hv ⊢
    simp only [Prod.fst_smul, Prod.snd_smul, Pi.smul_apply, smul_eq_mul]
    constructor; rw [(hv j hj).1]; ring; rw [(hv j hj).2]; ring

noncomputable def restrictToC (C : Finset (Fin n)) : supportSubmodule C →ₗ[α] (C → α) × (C → α) where
  toFun := fun ⟨v, _⟩ => (fun c => v.1 c.val, fun c => v.2 c.val)
  map_add' := fun ⟨v, _⟩ ⟨w, _⟩ => by simp [Prod.ext_iff]; constructor <;> ext <;> simp
  map_smul' := fun r ⟨v, _⟩ => by simp [Prod.ext_iff]; constructor <;> ext <;> simp

noncomputable def extendFromC (C : Finset (Fin n)) : (C → α) × (C → α) →ₗ[α] supportSubmodule C where
  toFun := fun ⟨f, g⟩ => ⟨(fun i => if h : i ∈ C then f ⟨i, h⟩ else 0,
                            fun i => if h : i ∈ C then g ⟨i, h⟩ else 0), by intro j hj; simp [hj]⟩
  map_add' := fun ⟨f₁, g₁⟩ ⟨f₂, g₂⟩ => by
    simp only [Prod.mk_add_mk]; apply Subtype.ext
    simp only [Submodule.coe_add, Prod.fst_add, Prod.snd_add, Pi.add_apply]
    constructor <;> ext i <;> split_ifs <;> simp
  map_smul' := fun r ⟨f, g⟩ => by
    simp only [Prod.smul_mk, RingHom.id_apply]; apply Subtype.ext
    simp only [Submodule.coe_smul, Prod.fst_smul, Prod.snd_smul, Pi.smul_apply, smul_eq_mul]
    constructor <;> ext i <;> split_ifs <;> simp

lemma restrictToC_extendFromC (C : Finset (Fin n)) : ∀ x, restrictToC C (extendFromC C x) = x := by
  intro ⟨f, g⟩; simp [restrictToC, extendFromC]; constructor <;> ext ⟨i, hi⟩ <;> simp [hi]

lemma extendFromC_restrictToC (C : Finset (Fin n)) : ∀ x, extendFromC C (restrictToC C x) = x := by
  intro ⟨v, hv⟩; simp [restrictToC, extendFromC]; apply Subtype.ext; simp only [Submodule.coe_mk]
  constructor <;> ext i <;> (split_ifs with h; rfl; exact (hv i h).1) <;> (split_ifs with h; rfl; exact (hv i h).2)

noncomputable def supportSubmoduleEquiv (C : Finset (Fin n)) : supportSubmodule C ≃ₗ[α] (C → α) × (C → α) where
  toFun := restrictToC C
  invFun := extendFromC C
  left_inv := extendFromC_restrictToC C
  right_inv := restrictToC_extendFromC C
  map_add' := (restrictToC C).map_add'
  map_smul' := (restrictToC C).map_smul'

lemma finrank_supportSubmodule (C : Finset (Fin n)) [FiniteDimensional α (SympVec n α)] :
    FiniteDimensional.finrank α (supportSubmodule C) = 2 * C.card := by
  rw [LinearEquiv.finrank_eq (supportSubmoduleEquiv C)]
  rw [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fun, FiniteDimensional.finrank_fun]; ring

/-! ## Symplectic Form Decomposition -/

lemma symplecticForm_decompose (p q : SympVec n α) (A B C : Finset (Fin n))
    (h_part : Disjoint A B ∧ Disjoint A C ∧ Disjoint B C) (h_union : A ∪ B ∪ C = Finset.univ) :
    symplecticForm p q = symplecticFormOn A p q + symplecticFormOn B p q + symplecticFormOn C p q := by
  classical
  set f := fun i : Fin n => p.1 i * q.2 i - p.2 i * q.1 i
  have hAB := h_part.1; have hAC := h_part.2.1; have hBC := h_part.2.2
  have hAC_left := Finset.disjoint_left.1 hAC; have hBC_left := Finset.disjoint_left.1 hBC
  have h_disj_union : Disjoint (A ∪ B) C := by
    refine Finset.disjoint_left.2 ?_; intro x hx hxC
    rcases Finset.mem_union.1 hx with hxA | hxB; exact hAC_left hxA hxC; exact hBC_left hxB hxC
  have h_symm : symplecticForm p q = ∑ i ∈ A ∪ B ∪ C, f i := by simp [symplecticForm, f, h_union]
  have h_split₁ : ∑ i ∈ A ∪ B ∪ C, f i = ∑ i ∈ A ∪ B, f i + ∑ i ∈ C, f i := by simpa using (Finset.sum_union h_disj_union (fun i : Fin n => f i))
  have h_split₂ : ∑ i ∈ A ∪ B, f i = ∑ i ∈ A, f i + ∑ i ∈ B, f i := by simpa using (Finset.sum_union hAB (fun i : Fin n => f i))
  have h_comb : ∑ i ∈ A ∪ B ∪ C, f i = (∑ i ∈ A, f i + ∑ i ∈ B, f i) + ∑ i ∈ C, f i := by simpa [h_split₂] using h_split₁
  have h_eval : (∑ i ∈ A, f i + ∑ i ∈ B, f i) + ∑ i ∈ C, f i = symplecticFormOn A p q + symplecticFormOn B p q + symplecticFormOn C p q := by simp [symplecticFormOn, f, add_comm, add_left_comm, add_assoc]
  simpa [symplecticFormOn, f, h_eval] using h_symm.trans h_comb

lemma symplecticForm_nondegenerate : ∀ u : SympVec n α, (∀ v : SympVec n α, symplecticForm u v = 0) → u = 0 := by
  intro u hu; ext i
  · let v : SympVec n α := ((fun _ => 0), (fun k => if k = i then 1 else 0))
    have hv := hu v; simp [symplecticForm] at hv
    rw [Finset.sum_eq_single i] at hv; simp at hv; exact hv
    intro b _ hb; simp [v]; have : b ≠ i := hb; simp [this]
    intro hi; exact (hi (Finset.mem_univ i)).elim
  · let v : SympVec n α := ((fun k => if k = i then 1 else 0), (fun _ => 0))
    have hv := hu v; simp [symplecticForm] at hv
    rw [Finset.sum_eq_single i] at hv; simp at hv; exact neg_eq_zero.mp hv
    intro b _ hb; simp [v]; have : b ≠ i := hb; simp [this]
    intro hi; exact (hi (Finset.mem_univ i)).elim

/-! ## Dimension of Symplectic Dual -/

lemma finrank_symplecticDual (S : Submodule α (SympVec n α)) [FiniteDimensional α (SympVec n α)] :
    FiniteDimensional.finrank α (symplecticDual S) = 2 * n - FiniteDimensional.finrank α S := by
  classical
  have h_total : FiniteDimensional.finrank α (SympVec n α) = 2 * n := by
    simp [SympVec]; rw [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fun, FiniteDimensional.finrank_fun]; ring
  let to_dual : SympVec n α →ₗ[α] Module.Dual α (SympVec n α) := symplecticBilin
  have h_ker : LinearMap.ker to_dual = ⊥ := by
    ext x; simp only [LinearMap.mem_ker, Submodule.mem_bot]; constructor
    · intro h; apply symplecticForm_nondegenerate x; intro v
      have := LinearMap.congr_fun h v; simp [to_dual, symplecticBilin] at this; exact this
    · intro h; simp [h]
  have h_dim_dual_ann : FiniteDimensional.finrank α S.dualAnnihilator = 2 * n - FiniteDimensional.finrank α S := by
    rw [Submodule.finrank_dualAnnihilator_eq, h_total]
  have h_eq : symplecticDual S = S.dualAnnihilator.comap to_dual := by
    ext v; simp only [symplecticDual, Submodule.mem_mk, Set.mem_setOf_eq, Submodule.mem_comap, Submodule.mem_dualAnnihilator]
    constructor
    · intro hv s hs; simp [to_dual, symplecticBilin]; exact hv s hs
    · intro hv s hs; have := hv ⟨s, hs⟩; simp [to_dual, symplecticBilin] at this; exact this
  rw [h_eq]
  have h_inj : Function.Injective to_dual := by rw [← LinearMap.ker_eq_bot]; exact h_ker
  rw [Submodule.finrank_comap_eq_of_injective to_dual h_inj]; exact h_dim_dual_ann

lemma finrank_logical_space (S : Stabilizer n α) [FiniteDimensional α (SympVec n α)] :
    FiniteDimensional.finrank α (symplecticDual S.S) - FiniteDimensional.finrank α S.S = 2 * quantum_code_dimension S.S := by
  classical
  simp only [quantum_code_dimension]
  have h_dual := finrank_symplecticDual S.S
  have h_total : FiniteDimensional.finrank α (SympVec n α) = 2 * n := by
    simp [SympVec]; rw [FiniteDimensional.finrank_prod, FiniteDimensional.finrank_fun, FiniteDimensional.finrank_fun]; ring
  rw [h_dual]
  have h_le : FiniteDimensional.finrank α S.S ≤ n := by
    have h_le_total : FiniteDimensional.finrank α S.S ≤ 2 * n := by rw [← h_total]; exact Submodule.finrank_le S.S
    have h_iso := stabilizer_le_symplecticDual S
    have h_iso_dim : FiniteDimensional.finrank α S.S ≤ FiniteDimensional.finrank α (symplecticDual S.S) := Submodule.finrank_mono h_iso
    rw [h_dual] at h_iso_dim; omega
  omega

/-! ## Symplectic Basis -/

structure SymplecticBasis (k : ℕ) (V : Submodule α (SympVec n α)) where
  X : Fin k → SympVec n α
  Z : Fin k → SympVec n α
  X_mem : ∀ i, X i ∈ V
  Z_mem : ∀ i, Z i ∈ V
  comm_XZ : ∀ i j, symplecticForm (X i) (Z j) = if i = j then 1 else 0
  anti_XX : ∀ i j, symplecticForm (X i) (X j) = 0
  anti_ZZ : ∀ i j, symplecticForm (Z i) (Z j) = 0

/-! ## Rank Bound -/

lemma rank_bound_from_commutators_simple (C : Finset (Fin n)) (k : ℕ)
    (X Z : Fin k → SympVec n α)
    (h_supp_X : ∀ i j, j ∉ C → (X i).1 j = 0 ∧ (X i).2 j = 0)
    (h_supp_Z : ∀ i j, j ∉ C → (Z i).1 j = 0 ∧ (Z i).2 j = 0)
    (h_comm : ∀ i j, symplecticForm (X i) (Z j) = if i = j then 1 else 0)
    (h_anti_X : ∀ i j, symplecticForm (X i) (X j) = 0)
    (h_anti_Z : ∀ i j, symplecticForm (Z i) (Z j) = 0)
    [FiniteDimensional α (SympVec n α)] : k ≤ C.card := by
  by_contra h_contra; push_neg at h_contra
  let vecs : Fin (2 * k) → SympVec n α := fun i => if h : i.val < k then X ⟨i.val, h⟩ else Z ⟨i.val - k, by omega⟩
  have h_lin_indep : LinearIndependent α vecs := by
    rw [linearIndependent_iff']; intro s l hl; intro i hi
    have h_sum_zero := hl
    by_cases h_lt : i.val < k
    · let m : Fin k := ⟨i.val, h_lt⟩
      have h_pair_Z : symplecticForm (∑ j ∈ s, l j • vecs j) (Z m) = 0 := by rw [h_sum_zero]; simp [symplecticForm]
      have h_expand : symplecticForm (∑ j ∈ s, l j • vecs j) (Z m) = ∑ j ∈ s, l j * symplecticForm (vecs j) (Z m) := symplecticForm_smul_sum_left s l vecs (Z m)
      rw [h_expand] at h_pair_Z
      have h_only_i : ∑ j ∈ s, l j * symplecticForm (vecs j) (Z m) = l i := by
        have h_i_mem : i ∈ s := hi
        rw [← Finset.add_sum_erase s _ h_i_mem]
        have h_vecs_i : vecs i = X m := by simp only [vecs, h_lt]; congr; ext; simp
        rw [h_vecs_i, h_comm m m]; simp only [↓reduceIte, mul_one]
        have h_rest_zero : ∑ j ∈ s.erase i, l j * symplecticForm (vecs j) (Z m) = 0 := by
          apply Finset.sum_eq_zero; intro j hj; simp at hj; have hj_ne := hj.2; simp only [vecs]
          split_ifs with h_j_lt
          · have h_pair : symplecticForm (X ⟨j.val, h_j_lt⟩) (Z m) = if ⟨j.val, h_j_lt⟩ = m then 1 else 0 := h_comm _ _
            have h_ne : j.val ≠ i.val := by intro h_eq; have : j = i := Fin.ext h_eq; exact hj_ne this
            have h_ne' : ⟨j.val, h_j_lt⟩ ≠ m := by intro h_eq; simp only [Fin.mk.injEq] at h_eq; exact h_ne h_eq
            simp only [h_ne', ↓reduceIte] at h_pair; rw [h_pair]; ring
          · have h_pair : symplecticForm (Z ⟨j.val - k, by omega⟩) (Z m) = 0 := h_anti_Z _ _; rw [h_pair]; ring
        rw [h_rest_zero, add_zero]
      rw [h_only_i] at h_pair_Z; exact h_pair_Z
    · push_neg at h_lt
      let m : Fin k := ⟨i.val - k, by omega⟩
      have h_pair_X : symplecticForm (∑ j ∈ s, l j • vecs j) (X m) = 0 := by rw [h_sum_zero]; simp [symplecticForm]
      have h_expand : symplecticForm (∑ j ∈ s, l j • vecs j) (X m) = ∑ j ∈ s, l j * symplecticForm (vecs j) (X m) := symplecticForm_smul_sum_left s l vecs (X m)
      rw [h_expand] at h_pair_X
      have h_only_i : ∑ j ∈ s, l j * symplecticForm (vecs j) (X m) = -l i := by
        have h_i_mem : i ∈ s := hi
        rw [← Finset.add_sum_erase s _ h_i_mem]
        have h_vecs_i : vecs i = Z m := by simp only [vecs]; have h_not_lt : ¬(i.val < k) := by omega; simp only [h_not_lt, ↓reduceDIte]; congr; ext; simp only [Fin.val_mk]
        rw [h_vecs_i]
        have h_anti : symplecticForm (Z m) (X m) = -symplecticForm (X m) (Z m) := by simp [symplecticForm]; rw [← Finset.sum_neg_distrib]; congr 1; ext j; ring
        rw [h_anti, h_comm m m]; simp only [↓reduceIte, neg_neg, mul_neg, mul_one]
        have h_rest_zero : ∑ j ∈ s.erase i, l j * symplecticForm (vecs j) (X m) = 0 := by
          apply Finset.sum_eq_zero; intro j hj; simp at hj; have hj_ne := hj.2; simp only [vecs]
          split_ifs with h_j_lt
          · have h_pair : symplecticForm (X ⟨j.val, h_j_lt⟩) (X m) = 0 := h_anti_X _ _; rw [h_pair]; ring
          · have h_anti' : symplecticForm (Z ⟨j.val - k, by omega⟩) (X m) = -symplecticForm (X m) (Z ⟨j.val - k, by omega⟩) := by simp [symplecticForm]; rw [← Finset.sum_neg_distrib]; congr 1; ext jj; ring
            rw [h_anti']
            have h_pair : symplecticForm (X m) (Z ⟨j.val - k, by omega⟩) = if m = ⟨j.val - k, by omega⟩ then 1 else 0 := h_comm _ _
            have h_ne : j.val ≠ i.val := by intro h_eq; have : j = i := Fin.ext h_eq; exact hj_ne this
            have h_ne' : m ≠ ⟨j.val - k, by omega⟩ := by intro h_eq; simp only [Fin.mk.injEq] at h_eq; omega
            simp only [h_ne', ↓reduceIte] at h_pair; rw [h_pair]; ring
        rw [h_rest_zero, add_zero]
      rw [h_only_i] at h_pair_X; linarith
  have h_in_supp : ∀ i, vecs i ∈ supportSubmodule C := by
    intro i; simp only [supportSubmodule, Submodule.mem_mk, Set.mem_setOf_eq, vecs]
    split_ifs with h; exact h_supp_X ⟨i.val, h⟩; exact h_supp_Z ⟨i.val - k, by omega⟩
  have h_span_le : Submodule.span α (Set.range vecs) ≤ supportSubmodule C := by
    apply Submodule.span_le.mpr; intro v hv; rcases hv with ⟨i, rfl⟩; exact h_in_supp i
  have h_finrank_span : FiniteDimensional.finrank α (Submodule.span α (Set.range vecs)) = 2 * k := by rw [LinearIndependent.finrank_span h_lin_indep]; simp [Fintype.card_fin]
  have h_finrank_supp : FiniteDimensional.finrank α (supportSubmodule C) = 2 * C.card := finrank_supportSubmodule C
  have h_finrank_le := Submodule.finrank_le_finrank h_span_le; omega

/-! ## Main Theorem -/

lemma quantum_singleton_bound_of_rank (n k d : ℕ) (S : Stabilizer n α)
    [FiniteDimensional α (SympVec n α)]
    (h_dim : k = quantum_code_dimension S.S) (h_rank : 2 * (d - 1) ≤ FiniteDimensional.finrank α S.S) :
    k ≤ n - 2 * (d - 1) := by
  classical
  have hk : k = n - FiniteDimensional.finrank α S.S := by simpa [quantum_code_dimension] using h_dim
  have h_le : n - FiniteDimensional.finrank α S.S ≤ n - 2 * (d - 1) := Nat.sub_le_sub_left h_rank n
  simpa [hk]

lemma quantum_singleton_bound_aux (n k d : ℕ) (S : Stabilizer n α) [FiniteDimensional α (SympVec n α)]
    (h_dim : k = quantum_code_dimension S.S) (h_dist : d ≤ quantum_distance S) (hd : 0 < d) (h_n_ge : n ≥ 2 * (d - 1))
    (A B C : Finset (Fin n)) (h_A_card : A.card = d - 1) (h_B_card : B.card = d - 1)
    (h_disj : Disjoint A B) (h_C_def : C = (A ∪ B)ᶜ)
    (X Z : Fin k → SympVec n α)
    (h_X_supp : ∀ i j, j ∉ C → (X i).1 j = 0 ∧ (X i).2 j = 0)
    (h_Z_supp : ∀ i j, j ∉ C → (Z i).1 j = 0 ∧ (Z i).2 j = 0)
    (h_comm : ∀ i j, symplecticForm (X i) (Z j) = if i = j then 1 else 0)
    (h_anti_X : ∀ i j, symplecticForm (X i) (X j) = 0)
    (h_anti_Z : ∀ i j, symplecticForm (Z i) (Z j) = 0) : k ≤ C.card :=
  rank_bound_from_commutators_simple C k X Z h_X_supp h_Z_supp h_comm h_anti_X h_anti_Z

lemma stabilizer_rank_ge_of_distance (n d : ℕ) (S : Stabilizer n α) [FiniteDimensional α (SympVec n α)]
    (h_dist : d ≤ quantum_distance S) (hd : 0 < d)
    (h_basis : ∀ k (A B C : Finset (Fin n)), k = quantum_code_dimension S.S →
      A.card = d - 1 → B.card = d - 1 → Disjoint A B → C = (A ∪ B)ᶜ →
      ∃ (X Z : Fin k → SympVec n α),
        (∀ i j, j ∉ C → (X i).1 j = 0 ∧ (X i).2 j = 0) ∧
        (∀ i j, j ∉ C → (Z i).1 j = 0 ∧ (Z i).2 j = 0) ∧
        (∀ i j, symplecticForm (X i) (Z j) = if i = j then 1 else 0) ∧
        (∀ i j, symplecticForm (X i) (X j) = 0) ∧
        (∀ i j, symplecticForm (Z i) (Z j) = 0)) : 2 * (d - 1) ≤ FiniteDimensional.finrank α S.S := by
  classical
  by_contra h_rank_low; push_neg at h_rank_low
  let r := FiniteDimensional.finrank α S.S
  have h_k : quantum_code_dimension S.S = n - r := rfl
  let k := n - r
  have h_k_bound : n - 2 * (d - 1) < k := by have : 2 * (d - 1) > r := h_rank_low; omega
  if h_n : 2 * (d - 1) ≤ n then
    let A : Finset (Fin n) := Finset.univ.filter (fun i => i.val < d - 1)
    let B : Finset (Fin n) := Finset.univ.filter (fun i => d - 1 ≤ i.val ∧ i.val < 2 * (d - 1))
    let C : Finset (Fin n) := (A ∪ B)ᶜ
    have h_A_card : A.card = d - 1 := by
      simp only [A, Finset.card_filter]
      have : (Finset.univ.filter (fun i : Fin n => i.val < d - 1)).card = (Finset.range (d - 1)).card := by
        apply Finset.card_bij (fun i _ => i.val)
        · intro i hi; simp at hi; exact Finset.mem_range.mpr hi
        · intro i₁ _ i₂ _ h; exact Fin.ext h
        · intro j hj; simp at hj; have hj' : j < n := by omega; exact ⟨⟨j, hj'⟩, by simp [hj], rfl⟩
      rw [this, Finset.card_range]
    have h_B_card : B.card = d - 1 := by
      simp only [B, Finset.card_filter]
      have : (Finset.univ.filter (fun i : Fin n => d - 1 ≤ i.val ∧ i.val < 2 * (d - 1))).card = (Finset.range (d - 1)).card := by
        apply Finset.card_bij (fun i _ => i.val - (d - 1))
        · intro i hi; simp at hi; exact Finset.mem_range.mpr (by omega)
        · intro i₁ hi₁ i₂ hi₂ h; simp at hi₁ hi₂; have : i₁.val = i₂.val := by omega; exact Fin.ext this
        · intro j hj; simp at hj; have hj' : d - 1 + j < n := by omega; exact ⟨⟨d - 1 + j, hj'⟩, by simp; omega, by omega⟩
      rw [this, Finset.card_range]
    have h_disj : Disjoint A B := by simp only [A, B, Finset.disjoint_filter]; intro i _ _; simp; omega
    have h_C_card : C.card = n - 2 * (d - 1) := by
      have h_union_card : (A ∪ B).card = 2 * (d - 1) := by rw [Finset.card_disjoint_union h_disj, h_A_card, h_B_card]; ring
      simp only [C]; rw [Finset.card_compl, Finset.card_fin, h_union_card]
    obtain ⟨X, Z, h_X_supp, h_Z_supp, h_comm, h_anti_X, h_anti_Z⟩ := h_basis k A B C rfl h_A_card h_B_card h_disj rfl
    have h_ineq := quantum_singleton_bound_aux n k d S rfl h_dist hd h_n A B C h_A_card h_B_card h_disj rfl X Z h_X_supp h_Z_supp h_comm h_anti_X h_anti_Z
    rw [h_C_card] at h_ineq; omega
  else
    push_neg at h_n; have h_r_le_n : r ≤ n := FiniteDimensional.finrank_le_card; omega

theorem quantum_singleton_bound (n k d : ℕ) (S : Stabilizer n α) [FiniteDimensional α (SympVec n α)]
    (h_dim : k = quantum_code_dimension S.S) (h_dist : 0 < d) (h_dist_le : d ≤ n) (h_code_dist : d ≤ quantum_distance S)
    (h_basis : ∀ k' (A B C : Finset (Fin n)), k' = quantum_code_dimension S.S →
      A.card = d - 1 → B.card = d - 1 → Disjoint A B → C = (A ∪ B)ᶜ →
      ∃ (X Z : Fin k' → SympVec n α),
        (∀ i j, j ∉ C → (X i).1 j = 0 ∧ (X i).2 j = 0) ∧
        (∀ i j, j ∉ C → (Z i).1 j = 0 ∧ (Z i).2 j = 0) ∧
        (∀ i j, symplecticForm (X i) (Z j) = if i = j then 1 else 0) ∧
        (∀ i j, symplecticForm (X i) (X j) = 0) ∧
        (∀ i j, symplecticForm (Z i) (Z j) = 0)) : k ≤ n - 2 * (d - 1) := by
  classical
  have h_rank := stabilizer_rank_ge_of_distance (n:=n) (d:=d) S h_code_dist h_dist h_basis
  exact quantum_singleton_bound_of_rank (n:=n) (k:=k) (d:=d) S h_dim h_rank

end CodingTheory
