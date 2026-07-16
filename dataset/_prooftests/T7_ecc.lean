import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.Algebra.NoZeroSMulDivisors.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.PicardGroup
import Mathlib.Data.Finset.Card

open scoped BigOperators

set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

set_option linter.unnecessarySimpa false

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
abbrev F (p : ℕ) [Fact p.Prime] := ZMod p
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
abbrev V (n p : ℕ) [Fact p.Prime] := (Fin n → F p) × (Fin n → F p)
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
def sym_form (u v : V n p) : F p :=
  Finset.univ.sum (fun i : Fin n => (u.1 i * v.2 i - u.2 i * v.1 i))
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_add_left (x y z : V n p) :
    sym_form (n:=n) (p:=p) (x + y) z = sym_form (n:=n) (p:=p) x z + sym_form (n:=n) (p:=p) y z := by
  classical
  unfold sym_form
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have h : (fun i : Fin n => (x.1 i + y.1 i) * z.2 i - (x.2 i + y.2 i) * z.1 i) =
           (fun i : Fin n => (x.1 i * z.2 i - x.2 i * z.1 i) + (y.1 i * z.2 i - y.2 i * z.1 i)) := by
    ext i
    ring
  rw [h]
  exact Finset.sum_add_distrib
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_add_right (x y z : V n p) :
    sym_form (n:=n) (p:=p) x (y + z) = sym_form (n:=n) (p:=p) x y + sym_form (n:=n) (p:=p) x z := by
  classical
  unfold sym_form
  simp only [Prod.fst_add, Prod.snd_add, Pi.add_apply]
  have h : (fun i : Fin n => x.1 i * (y.2 i + z.2 i) - x.2 i * (y.1 i + z.1 i)) =
           (fun i : Fin n => (x.1 i * y.2 i - x.2 i * y.1 i) + (x.1 i * z.2 i - x.2 i * z.1 i)) := by
    ext i
    ring
  rw [h]
  exact Finset.sum_add_distrib
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_smul_left (c : F p) (x y : V n p) :
    sym_form (n:=n) (p:=p) (c • x) y = c * sym_form (n:=n) (p:=p) x y := by
  classical
  unfold sym_form
  have h1 :
      (∑ i : Fin n, c * x.1 i * y.2 i)
        = c * (∑ i : Fin n, x.1 i * y.2 i) := by
    change (Finset.univ.sum (fun i : Fin n => c * x.1 i * y.2 i))
        = c * (Finset.univ.sum (fun i : Fin n => x.1 i * y.2 i))
    have hs :
        (fun i : Fin n => c * x.1 i * y.2 i)
          = (fun i : Fin n => c * (x.1 i * y.2 i)) := by
      funext i
      simp [mul_assoc]
    rw [hs]
    rw [← Finset.mul_sum]


  have h2 :
      (∑ i : Fin n, c * x.2 i * y.1 i)
        = c * (∑ i : Fin n, x.2 i * y.1 i) := by
    change (Finset.univ.sum (fun i : Fin n => c * x.2 i * y.1 i))
        = c * (Finset.univ.sum (fun i : Fin n => x.2 i * y.1 i))
    have hs :
        (fun i : Fin n => c * x.2 i * y.1 i)
          = (fun i : Fin n => c * (x.2 i * y.1 i)) := by
      funext i
      simp [mul_assoc]
    rw [hs]
    rw [← Finset.mul_sum]

  simp [h1, h2, mul_sub]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_smul_right (c : F p) (x y : V n p) :
    sym_form (n:=n) (p:=p) x (c • y) = c * sym_form (n:=n) (p:=p) x y := by
  classical
  unfold sym_form

  have h1 :
      (∑ i : Fin n, x.1 i * (c * y.2 i))
        = c * (∑ i : Fin n, x.1 i * y.2 i) := by
    change (Finset.univ.sum (fun i : Fin n => x.1 i * (c * y.2 i)))
        = c * (Finset.univ.sum (fun i : Fin n => x.1 i * y.2 i))
    have hs :
        (fun i : Fin n => x.1 i * (c * y.2 i))
          = (fun i : Fin n => c * (x.1 i * y.2 i)) := by
      funext i
      simp [mul_left_comm]
    rw [hs]
    rw [← Finset.mul_sum]


  have h2 :
      (∑ i : Fin n, x.2 i * (c * y.1 i))
        = c * (∑ i : Fin n, x.2 i * y.1 i) := by
    change (Finset.univ.sum (fun i : Fin n => x.2 i * (c * y.1 i)))
        = c * (Finset.univ.sum (fun i : Fin n => x.2 i * y.1 i))
    have hs :
        (fun i : Fin n => x.2 i * (c * y.1 i))
          = (fun i : Fin n => c * (x.2 i * y.1 i)) := by
      funext i
      simp [mul_assoc, mul_comm]
    rw [hs]
    rw [← Finset.mul_sum]


  simp [h1, h2, mul_sub]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_swap (u v : V n p) :
    sym_form u v = - sym_form v u := by
  unfold sym_form
  rw [← Finset.sum_neg_distrib]
  congr with i
  ring
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
noncomputable def symB : LinearMap.BilinForm (F p) (V n p) :=
  LinearMap.mk₂ (F p) (fun x y => sym_form (n:=n) (p:=p) x y)
    (by intro x y z; simpa using sym_form_add_left (n:=n) (p:=p) x y z)
    (by intro c x y; simpa using sym_form_smul_left (n:=n) (p:=p) c x y)
    (by intro x y z; simpa using sym_form_add_right (n:=n) (p:=p) x y z)
    (by intro c x y; simpa using sym_form_smul_right (n:=n) (p:=p) c x y)
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
@[simp] lemma symB_apply (x y : V n p) :
    symB (n:=n) (p:=p) x y = sym_form (n:=n) (p:=p) x y := rfl
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_nondegenerate (u : V n p) (h : ∀ v, sym_form u v = 0) : u = 0 := by
  have h_cases : ∀ (i : Fin n), u.1 i = 0 ∧ u.2 i = 0 := by
    intro i
    have h1 : u.1 i = 0 := by
      specialize h ⟨ 0, fun j => if j = i then 1 else 0 ⟩ ; simp_all +decide [ sym_form ] ;
    have h2 : u.2 i = 0 := by
      specialize h ⟨ fun j => if j = i then 1 else 0, 0 ⟩ ; simp_all +decide [ sym_form ] ;
    exact ⟨h1, h2⟩;
  exact Prod.ext ( funext fun i => h_cases i |>.1 ) ( funext fun i => h_cases i |>.2 )
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
def V_sub (C : Finset (Fin n)) : Submodule (F p) (V n p) where
  carrier := {v | ∀ i ∉ C, v.1 i = 0 ∧ v.2 i = 0}
  add_mem' := by
    intro a b a_1 a_2
    simp_all only [Set.mem_setOf_eq, Prod.fst_add, Pi.add_apply, not_false_eq_true, add_zero, Prod.snd_add, and_self,
      implies_true]
  zero_mem' := by
    simp_all only [Set.mem_setOf_eq, Prod.fst_zero, Pi.zero_apply, Prod.snd_zero, and_self, implies_true]
  smul_mem' := by
    intro c x a
    simp_all only [Set.mem_setOf_eq, Prod.smul_fst, Pi.smul_apply, not_false_eq_true, smul_eq_mul, mul_zero,
      Prod.smul_snd, and_self, implies_true]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
noncomputable def restrictToC (C : Finset (Fin n)) :
    V_sub (p:=p) C →ₗ[F p] (C → F p) × (C → F p) where
  toFun := fun ⟨v, _⟩ => (fun c => v.1 c.1, fun c => v.2 c.1)
  map_add' := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    ext c <;> simp
  map_smul' := by
    intro r x
    rcases x with ⟨x, hx⟩
    ext c <;> simp
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
noncomputable def extendFromC (C : Finset (Fin n)) :
    (C → F p) × (C → F p) →ₗ[F p] V_sub (p:=p) C where
  toFun := fun ⟨f, g⟩ =>
    ⟨ ((fun i => if h : i ∈ C then f ⟨i, h⟩ else 0),
       (fun i => if h : i ∈ C then g ⟨i, h⟩ else 0)),
      by
        intro j hj
        constructor <;> simp [hj] ⟩
  map_add' := by
    classical
    rintro ⟨f1, g1⟩ ⟨f2, g2⟩
    apply Subtype.ext
    ext i <;> by_cases hi : i ∈ C <;> simp [hi]
  map_smul' := by
    classical
    intro r x
    rcases x with ⟨f, g⟩
    apply Subtype.ext
    ext i <;> by_cases hi : i ∈ C <;> simp [hi]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma restrictToC_extendFromC (C : Finset (Fin n)) :
    ∀ x, restrictToC (p:=p) C (extendFromC (p:=p) C x) = x := by
  classical
  rintro ⟨f, g⟩
  apply Prod.ext
  · funext c; simp [restrictToC, extendFromC]
  · funext c; simp [restrictToC, extendFromC]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma extendFromC_restrictToC (C : Finset (Fin n)) :
    ∀ x, extendFromC (p:=p) C (restrictToC (p:=p) C x) = x := by
  classical
  rintro ⟨v, hv⟩
  have hv' : ∀ j, j ∉ C → v.1 j = 0 ∧ v.2 j = 0 := by
    simpa [V_sub] using hv
  apply Subtype.ext
  ext i
  · by_cases hi : i ∈ C
    · simp [extendFromC, restrictToC, hi]
    · have h0 := (hv' i hi).1
      simp [extendFromC, restrictToC, hi, h0]
  · by_cases hi : i ∈ C
    · simp [extendFromC, restrictToC, hi]
    · have h0 := (hv' i hi).2
      simp [extendFromC, restrictToC, hi, h0]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
noncomputable def V_sub_iso (C : Finset (Fin n)) :
    V_sub (p:=p) C ≃ₗ[F p] (C → F p) × (C → F p) where
  toFun := restrictToC (p:=p) C
  invFun := extendFromC (p:=p) C
  left_inv := extendFromC_restrictToC (p:=p) C
  right_inv := restrictToC_extendFromC (p:=p) C
  map_add' := (restrictToC (p:=p) C).map_add'
  map_smul' := (restrictToC (p:=p) C).map_smul'
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma dim_V_sub (C : Finset (Fin n)) : Module.finrank (F p) (V_sub (p:=p) C) = 2 * C.card := by
  classical
  -- finrank preserved by linear equivalence
  simpa [Module.finrank_prod, two_mul] using
    (LinearEquiv.finrank_eq (V_sub_iso (n:=n) (p:=p) C))
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
def r_E (E : Finset (Fin n)) : V n p →ₗ[F p] V_sub (p:=p) E where
  toFun v := ⟨(fun i => if i ∈ E then v.1 i else 0, fun i => if i ∈ E then v.2 i else 0), by
    exact fun i hi => by simp_all only [↓reduceIte, and_self];⟩
  map_add' := by
    intro x y
    simp_all only [Prod.fst_add, Pi.add_apply, Prod.snd_add]
    obtain ⟨fst, snd⟩ := x
    obtain ⟨fst_1, snd_1⟩ := y
    simp_all only [AddMemClass.mk_add_mk, Prod.mk_add_mk, Subtype.mk.injEq, Prod.mk.injEq]
    apply And.intro
    · ext x : 1
      simp_all only [Pi.add_apply]
      split
      next h => simp_all only
      next h => simp_all only [add_zero]
    · ext x : 1
      simp_all only [Pi.add_apply]
      split
      next h => simp_all only
      next h => simp_all only [add_zero]
  map_smul' := by
    intro m x
    simp_all only [Prod.smul_fst, Pi.smul_apply, smul_eq_mul, Prod.smul_snd, RingHom.id_apply]
    obtain ⟨fst, snd⟩ := x
    simp_all only [SetLike.mk_smul_mk, Prod.smul_mk, Subtype.mk.injEq, Prod.mk.injEq]
    apply And.intro
    · ext x : 1
      simp_all only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero]
    · ext x : 1
      simp_all only [Pi.smul_apply, smul_eq_mul, mul_ite, mul_zero]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
abbrev sym_orth (S : Submodule (F p) (V n p)) : Submodule (F p) (V n p) :=
  (symB (n:=n) (p:=p)).orthogonal S
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
def IsIsotropic (S : Submodule (F p) (V n p)) : Prop :=
  S ≤ sym_orth S
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
def S_M (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) : Submodule (F p) (V n p) :=
  S ⊓ V_sub (p:=p) M
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
def S_perp_M (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) : Submodule (F p) (V n p) :=
  sym_orth S ⊓ V_sub (p:=p) M
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
noncomputable def g (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) : ℕ :=
  Module.finrank (F p) (S_perp_M S M) - Module.finrank (F p) (S_M S M)
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma ker_r_E (E : Finset (Fin n)) :
    LinearMap.ker (r_E (p:=p) E) = V_sub (p:=p) (Finset.univ \ E) := by
  classical
  ext x
  constructor
  · intro hx
    have hx0 : (r_E (p:=p) E) x = 0 := by
      simpa [LinearMap.mem_ker] using hx

    have hxval : ((r_E (p:=p) E) x : V n p) = 0 :=
      congrArg Subtype.val hx0

    have hx1fun :
        (fun i : Fin n => if i ∈ E then x.1 i else 0) = 0 := by
      simpa [r_E] using congrArg Prod.fst hxval
    have hx2fun :
        (fun i : Fin n => if i ∈ E then x.2 i else 0) = 0 := by
      simpa [r_E] using congrArg Prod.snd hxval

    intro i hi
    have hiE : i ∈ E := by
      simpa [Finset.mem_sdiff, Finset.mem_univ] using hi
    constructor
    · have hx1i : (if i ∈ E then x.1 i else 0) = 0 :=
        congrArg (fun f => f i) hx1fun
      simpa [hiE] using hx1i
    · have hx2i : (if i ∈ E then x.2 i else 0) = 0 :=
        congrArg (fun f => f i) hx2fun
      simpa [hiE] using hx2i

  · intro hx

    have hfx : (r_E (p:=p) E) x = 0 := by
      ext i <;> by_cases hi : i ∈ E
      ·
        have hnot : i ∉ (Finset.univ \ E) := by
          simp [Finset.mem_sdiff, Finset.mem_univ, hi]

        simpa [r_E, hi] using (hx i hnot).1
      ·
        simp [r_E, hi]
      ·
        have hnot : i ∉ (Finset.univ \ E) := by
          simp [Finset.mem_sdiff, Finset.mem_univ, hi]
        simpa [r_E, hi] using (hx i hnot).2
      ·
        simp [r_E, hi]

    simpa [LinearMap.mem_ker] using hfx
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
def E_c (E : Finset (Fin n)) : Finset (Fin n) := Eᶜ
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma dim_map_r_E (S : Submodule (F p) (V n p)) (E : Finset (Fin n)) :
    Module.finrank (F p) ↥(S.map (r_E E)) = Module.finrank (F p) ↥S - Module.finrank (F p) ↥(S ⊓ V_sub (p:=p) (E_c E)) := by
      have h_rank_nullity : Module.finrank (F p) (↥(S.map (r_E E))) = Module.finrank (F p) S - Module.finrank (F p) (↥(S ⊓ LinearMap.ker (r_E E))) := by
        have h_rank_nullity : ∀ (f : (V n p) →ₗ[F p] V_sub (p:=p) E), Module.finrank (F p) (↥(Submodule.map f S)) = Module.finrank (F p) S - Module.finrank (F p) (↥(S ⊓ LinearMap.ker f)) := by
          intro f
          have h_rank_nullity : ∀ (f : (V n p) →ₗ[F p] V_sub (p:=p) E), Module.finrank (F p) (↥(Submodule.map f S)) = Module.finrank (F p) S - Module.finrank (F p) (↥(S ⊓ LinearMap.ker f)) := by
            intro f
            have h_rank_nullity : ∀ (f : (V n p) →ₗ[F p] V_sub (p:=p) E), ∀ (U : Submodule (F p) (V n p)), Module.finrank (F p) (↥(Submodule.map f U)) = Module.finrank (F p) U - Module.finrank (F p) (↥(U ⊓ LinearMap.ker f)) := by
              intros f U
              have h_rank_nullity : Module.finrank (F p) (↥(Submodule.map f U)) = Module.finrank (F p) U - Module.finrank (F p) (↥(LinearMap.ker (f.comp (Submodule.subtype U)))) := by
                have := LinearMap.finrank_range_add_finrank_ker ( f.comp ( Submodule.subtype U ) );
                exact eq_tsub_of_add_eq <| by rw [ show LinearMap.range ( f ∘ₗ U.subtype ) = Submodule.map f U from by ext; aesop ] at this; linarith;
              convert h_rank_nullity using 3;
              rw [ ← Submodule.finrank_map_subtype_eq ];
              congr ; ext ;
              rename_i x
              simp_all only [Submodule.mem_inf, LinearMap.mem_ker, Submodule.mem_map, LinearMap.coe_comp,
                Submodule.coe_subtype, Function.comp_apply, Submodule.subtype_apply, Subtype.exists, exists_and_left,
                exists_prop, exists_eq_right_right]
              obtain ⟨fst, snd⟩ := x
              apply Iff.intro
              · intro a
                simp_all only [and_self]
              · intro a
                simp_all only [and_self];
              · ext ; aesop;
              · ext ; aesop;
              · infer_instance
            exact h_rank_nullity f S;
          exact h_rank_nullity f;
        convert h_rank_nullity ( r_E E ) using 1;
      rwa [ show LinearMap.ker ( r_E E ) = V_sub ( E_c E ) from ?_ ] at h_rank_nullity;
      convert ker_r_E E using 1
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_r_E (M : Finset (Fin n)) (v : V n p) (hv : v ∈ V_sub (p:=p) M) (s : V n p) :
    sym_form v s = sym_form v (r_E M s) := by
      refine' Finset.sum_congr rfl fun i hi => _;
      by_cases hi' : i ∈ M <;> simp_all +decide [ r_E ];
      cases hv i hi' ; simp_all only [zero_mul, sub_self]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
def r_E_V (E : Finset (Fin n)) : V n p →ₗ[F p] V n p :=
  (V_sub (p:=p) E).subtype.comp (r_E E)
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_nondegenerate_on_V_sub (M : Finset (Fin n)) (v : V n p)
    (hv : v ∈ V_sub (p:=p) M)
    (h : ∀ w : V n p, w ∈ V_sub (p:=p) M → sym_form (n:=n) (p:=p) v w = 0) :
    v = 0 := by
  apply sym_form_nondegenerate (n:=n) (p:=p) v
  intro w
  have hw0 :
      sym_form (n:=n) (p:=p) v (↑(r_E (n:=n) (p:=p) M w) : V n p) = 0 :=
    h (↑(r_E (n:=n) (p:=p) M w) : V n p)
      (by simpa using (r_E (n:=n) (p:=p) M w).property)
  simpa [sym_form_r_E (n:=n) (p:=p) M v hv w] using hw0
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
  lemma sym_form_left_restrict (M : Finset (Fin n)) (s v : V n p)
    (hv : v ∈ V_sub (p:=p) M) :
    sym_form (n:=n) (p:=p) ((r_E_V (n:=n) (p:=p) M) s) v = sym_form (n:=n) (p:=p) s v := by
  classical
  unfold r_E_V
  unfold sym_form r_E
  refine Finset.sum_congr rfl ?_
  intro i hi
  by_cases hiM : i ∈ M
  · simp [hiM]
  · have hv0 := hv i hiM
    simp [hiM, hv0.1, hv0.2]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma orth_inter_eq_orth_map (M : Finset (Fin n)) (S : Submodule (F p) (V n p)) :
    sym_orth (n:=n) (p:=p) S ⊓ V_sub (p:=p) M
      = sym_orth (n:=n) (p:=p) (S.map (r_E_V (n:=n) (p:=p) M)) ⊓ V_sub (p:=p) M := by
  classical
  ext v
  constructor
  · rintro ⟨hvS, hvM⟩
    refine ⟨?_, hvM⟩
    rintro _ ⟨s, hs, rfl⟩
    have hs0 : sym_form (n:=n) (p:=p) s v = 0 := by
      simpa using hvS s hs
    have hpair :
        sym_form (n:=n) (p:=p) ((r_E_V (n:=n) (p:=p) M) s) v
          = sym_form (n:=n) (p:=p) s v :=
      sym_form_left_restrict (n:=n) (p:=p) M s v hvM

    simp [LinearMap.BilinForm.IsOrtho, symB_apply, hpair]
    exact hs0

  · rintro ⟨hvMap, hvM⟩
    refine ⟨?_, hvM⟩
    intro s hs
    have h0 : sym_form (n:=n) (p:=p) ((r_E_V (n:=n) (p:=p) M) s) v = 0 := by
      simpa using hvMap ((r_E_V (n:=n) (p:=p) M) s) (Submodule.mem_map_of_mem hs)
    have hpair :
        sym_form (n:=n) (p:=p) ((r_E_V (n:=n) (p:=p) M) s) v
          = sym_form (n:=n) (p:=p) s v :=
      sym_form_left_restrict (n:=n) (p:=p) M s v hvM
    -- goal is sym_form s v = 0
    simpa [hpair] using h0
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
noncomputable def symB_sub (M : Finset (Fin n)) : LinearMap.BilinForm (F p) (V_sub (p:=p) M) :=
  (symB (n:=n) (p:=p)).comp (V_sub (p:=p) M).subtype (V_sub (p:=p) M).subtype
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
abbrev sym_form_sub (M : Finset (Fin n)) :
    LinearMap.BilinForm (F p) ↥(V_sub (p:=p) M) :=
  symB_sub (n:=n) (p:=p) M
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
@[simp] lemma sym_form_sub_apply (M : Finset (Fin n))
    (x y : ↥(V_sub (p:=p) M)) :
    sym_form_sub (n:=n) (p:=p) M x y
      = sym_form (n:=n) (p:=p) (x : V n p) (y : V n p) := rfl
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_sub_nondegenerate (M : Finset (Fin n)) :
    (sym_form_sub (p:=p) M).Nondegenerate := by
      intro v hv
      apply Classical.byContradiction
      intro hv_nonzero;
      obtain ⟨w, hw⟩ : ∃ w : V_sub (p:=p) M, sym_form v.1 w.1 ≠ 0 := by
        convert sym_form_nondegenerate_on_V_sub M v.1 v.2 using 1;
        simp +zetaDelta at *;
        grind;
      exact hw ( hv w )
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma orth_inter_eq_orth_sub_image (M : Finset (Fin n)) (S : Submodule (F p) (V n p)) :
    sym_orth S ⊓ V_sub (p:=p) M = ((sym_form_sub (p:=p) M).orthogonal (S.map (r_E M))).map (V_sub (p:=p) M).subtype := by
  classical
  convert orth_inter_eq_orth_map M S using 1;
  ext; simp [sym_form_sub];
  simp +decide [ symB, LinearMap.BilinForm.IsOrtho ];
  simp +decide [ r_E_V, Subtype.ext_iff ];
  grind
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma sym_form_sub_isRefl (M : Finset (Fin n)) :
    (sym_form_sub (n:=n) (p:=p) M).IsRefl := by
  intro v w h
  have h' :
      sym_form (n:=n) (p:=p) (v : V n p) (w : V n p) = 0 := by
    simpa [sym_form_sub_apply] using h

  have hwv :
      sym_form (n:=n) (p:=p) (w : V n p) (v : V n p) = 0 := by
    calc
      sym_form (n:=n) (p:=p) (w : V n p) (v : V n p)
          = - sym_form (n:=n) (p:=p) (v : V n p) (w : V n p) := by
              simpa using
                (sym_form_swap (n:=n) (p:=p)
                  (u := (w : V n p)) (v := (v : V n p)))
      _ = 0 := by simpa [h']

  -- go back down to the restricted form
  simpa [sym_form_sub_apply] using hwv
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma dim_orth_inter (M : Finset (Fin n)) (S : Submodule (F p) (V n p)) :
    Module.finrank (F p) ↥(sym_orth S ⊓ V_sub (p:=p) M) = 2 * M.card - Module.finrank (F p) ↥(S.map (r_E M)) := by
      have h_image : sym_orth S ⊓ V_sub M = ((sym_form_sub M).orthogonal (S.map (r_E M))).map (V_sub M).subtype := by
        convert orth_inter_eq_orth_sub_image M S using 1;
      have h_orthogonal_complement : ∀ (W : Submodule (F p) (V_sub (p:=p) M)), Module.finrank (F p) ((sym_form_sub M).orthogonal W) = Module.finrank (F p) (V_sub (p:=p) M) - Module.finrank (F p) W := by
        have h_orthogonal_complement : ∀ (W : Submodule (F p) (V_sub (p:=p) M)), (sym_form_sub (p:=p) M).IsRefl → (sym_form_sub (p:=p) M).Nondegenerate → Module.finrank (F p) ((sym_form_sub (p:=p) M).orthogonal W) = Module.finrank (F p) (V_sub (p:=p) M) - Module.finrank (F p) W := by
          exact fun W a a_1 => LinearMap.BilinForm.finrank_orthogonal a_1 a W;
        exact fun W => h_orthogonal_complement W ( sym_form_sub_isRefl M ) ( sym_form_sub_nondegenerate M );
      convert h_orthogonal_complement ( S.map ( r_E M ) ) using 1;
      · rw [ h_image, ← Submodule.finrank_map_subtype_eq ];
      · rw [ dim_V_sub ]
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma g_expansion (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M = 2 * M.card + Module.finrank (F p) (S_M S (E_c M)) - Module.finrank (F p) S - Module.finrank (F p) (S_M S M) := by
      have h_g : g S M = 2 * M.card - Module.finrank (F p) (S.map (r_E M)) - Module.finrank (F p) (S_M S M) := by
        unfold g;
        rw [ show S_perp_M S M = sym_orth S ⊓ V_sub ( p := p ) M from rfl, dim_orth_inter ];
      -- By definition of $r_E$, we know that
      have h_dim_map : Module.finrank (F p) (S.map (r_E M)) = Module.finrank (F p) S - Module.finrank (F p) (S_M S (E_c M)) := by
        convert dim_map_r_E S M using 1;
      rw [ h_g, h_dim_map, tsub_tsub ];
      rw [ tsub_tsub, add_comm ];
      rw [ tsub_eq_of_eq_add ];
      rw [ tsub_add_eq_add_tsub ];
      · rw [ Nat.sub_eq_of_eq_add ];
        rw [ ← add_assoc, add_comm ];
        rw [ tsub_add_eq_add_tsub ];
        · exact Nat.sub_eq_of_eq_add <| by ring;
        · exact Submodule.finrank_mono <| inf_le_left;
      · have h_dim_S_map : Module.finrank (F p) (S.map (r_E M)) ≤ 2 * M.card := by
          have h_dim_S_map : Module.finrank (F p) (S.map (r_E M)) ≤ Module.finrank (F p) (V_sub (p:=p) M) := by
            apply_rules [ Submodule.finrank_le ];
          exact h_dim_S_map.trans ( by rw [ dim_V_sub ] );
        have h_dim_S_M : Module.finrank (F p) (S_M S M) ≤ 2 * M.card - Module.finrank (F p) (S.map (r_E M)) := by
          have h_dim_S_M : Module.finrank (F p) (S_perp_M S M) = 2 * M.card - Module.finrank (F p) (S.map (r_E M)) := by
            convert dim_orth_inter M S using 1;
          refine' h_dim_S_M ▸ Submodule.finrank_mono _;
          exact fun x hx => ⟨ hS hx.1, hx.2 ⟩;
        omega
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma dim_S_M_add_dim_S_M_c_le_dim_S (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) :
    Module.finrank (F p) (S_M S M) + Module.finrank (F p) (S_M S (E_c M)) ≤ Module.finrank (F p) S := by
      rw [ ← Submodule.finrank_sup_add_finrank_inf_eq ];
      have h_sum_subset : S_M S M ⊔ S_M S (E_c M) ≤ S := by
        exact sup_le ( inf_le_left ) ( inf_le_left );
      refine' le_trans ( add_le_add_right ( Submodule.finrank_mono h_sum_subset ) _ ) _;
      simp +decide [ S_M ];
      simp +decide [ Submodule.eq_bot_iff, V_sub ];
      simp_all +decide [ E_c, funext_iff ];
      exact fun a b ha ha' ha'' => ⟨ fun i => if hi : i ∈ M then ha'' i hi |>.1 else ha' i hi |>.1, fun i => if hi : i ∈ M then ha'' i hi |>.2 else ha' i hi |>.2 ⟩
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma g_formula (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M = (2 * M.card + Module.finrank (F p) (S_M S (E_c M))) - (Module.finrank (F p) S + Module.finrank (F p) (S_M S M)) := by
      convert g_expansion S hS M using 1;
      grind
end

noncomputable section
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
variable {n : ℕ} {p : ℕ} [Fact p.Prime]
lemma g_add_dims (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M + Module.finrank (F p) (S_M S M) + Module.finrank (F p) S = 2 * M.card + Module.finrank (F p) (S_M S (E_c M)) := by
      -- By definition of $g(S, E)$, we know that
      have h_g_def := g_formula (n:=n) (p:=p) S hS M
      have := dim_S_M_add_dim_S_M_c_le_dim_S S M;
      contrapose! h_g_def;
      rw [ Ne.eq_def, eq_tsub_iff_add_eq_of_le ];
      · cases lt_or_gt_of_ne h_g_def <;> linarith;
      · have := dim_orth_inter M S;
        have := dim_map_r_E S M;
        unfold S_M at *;
        rw [ eq_tsub_iff_add_eq_of_le ] at *;
        · linarith [ show Module.finrank ( F p ) ↥ ( S ⊓ V_sub M ) ≤ Module.finrank ( F p ) ↥ ( sym_orth S ⊓ V_sub M ) from Submodule.finrank_mono <| by
                      exact inf_le_inf_right (V_sub M) hS ];
        · have := Submodule.finrank_le ( Submodule.map ( r_E M ) S );
          exact le_trans this ( by rw [ dim_V_sub ] );
        · (expose_names; exact Nat.le_of_add_left_le this_1)
end
