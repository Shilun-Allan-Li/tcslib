
import Mathlib
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

/-
Definition of the symplectic vector space V and the standard symplectic form.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

abbrev F (p : ℕ) [Fact p.Prime] := ZMod p

/-- The symplectic vector space V := F^n × F^n -/
abbrev V (n p : ℕ) [Fact p.Prime] := (Fin n → F p) × (Fin n → F p)

/-- Standard symplectic form on V -/

def sym_form (u v : V n p) : F p :=
  Finset.univ.sum (fun i : Fin n => (u.1 i * v.2 i - u.2 i * v.1 i))
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




lemma sym_form_swap (u v : V n p) :
    sym_form u v = - sym_form v u := by
  unfold sym_form
  rw [← Finset.sum_neg_distrib]
  congr with i
  ring




noncomputable def symB : LinearMap.BilinForm (F p) (V n p) :=
  LinearMap.mk₂ (F p) (fun x y => sym_form (n:=n) (p:=p) x y)
    (by intro x y z; simpa using sym_form_add_left (n:=n) (p:=p) x y z)
    (by intro c x y; simpa using sym_form_smul_left (n:=n) (p:=p) c x y)
    (by intro x y z; simpa using sym_form_add_right (n:=n) (p:=p) x y z)
    (by intro c x y; simpa using sym_form_smul_right (n:=n) (p:=p) c x y)

@[simp] lemma symB_apply (x y : V n p) :
    symB (n:=n) (p:=p) x y = sym_form (n:=n) (p:=p) x y := rfl






lemma sym_form_nondegenerate (u : V n p) (h : ∀ v, sym_form u v = 0) : u = 0 := by
  have h_cases : ∀ (i : Fin n), u.1 i = 0 ∧ u.2 i = 0 := by
    intro i
    have h1 : u.1 i = 0 := by
      specialize h ⟨ 0, fun j => if j = i then 1 else 0 ⟩ ; simp_all +decide [ sym_form ] ;
    have h2 : u.2 i = 0 := by
      specialize h ⟨ fun j => if j = i then 1 else 0, 0 ⟩ ; simp_all +decide [ sym_form ] ;
    exact ⟨h1, h2⟩;
  exact Prod.ext ( funext fun i => h_cases i |>.1 ) ( funext fun i => h_cases i |>.2 )

/-
Definition of support, weight, and support subspace V_C.
-/
/-- Support of a vector v in V -/
def supp (v : V n p) : Finset (Fin n) :=
  {i | v.1 i ≠ 0 ∨ v.2 i ≠ 0}.toFinset

/-- Weight of a vector v in V -/
def wt (v : V n p) : ℕ := (supp v).card

/-- Support subspace V_C -/
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

/-
Isomorphism between V_C and F^|C| x F^|C|.
-/
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

lemma restrictToC_extendFromC (C : Finset (Fin n)) :
    ∀ x, restrictToC (p:=p) C (extendFromC (p:=p) C x) = x := by
  classical
  rintro ⟨f, g⟩
  apply Prod.ext
  · funext c; simp [restrictToC, extendFromC]
  · funext c; simp [restrictToC, extendFromC]

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

noncomputable def V_sub_iso (C : Finset (Fin n)) :
    V_sub (p:=p) C ≃ₗ[F p] (C → F p) × (C → F p) where
  toFun := restrictToC (p:=p) C
  invFun := extendFromC (p:=p) C
  left_inv := extendFromC_restrictToC (p:=p) C
  right_inv := restrictToC_extendFromC (p:=p) C
  map_add' := (restrictToC (p:=p) C).map_add'
  map_smul' := (restrictToC (p:=p) C).map_smul'


/-
Dimension of a support subspace V_C is 2|C|.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

lemma dim_V_sub (C : Finset (Fin n)) : Module.finrank (F p) (V_sub (p:=p) C) = 2 * C.card := by
  classical
  -- finrank preserved by linear equivalence
  simpa [Module.finrank_prod, two_mul] using
    (LinearEquiv.finrank_eq (V_sub_iso (n:=n) (p:=p) C))


/-
Definition of restriction map r_E.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Restriction map r_E : V -> V_E -/
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

/-
Definitions of symplectic orthogonal complement, isotropic subspace, and code distance.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Orthogonal complement with respect to the symplectic bilinear form. -/
abbrev sym_orth (S : Submodule (F p) (V n p)) : Submodule (F p) (V n p) :=
  (symB (n:=n) (p:=p)).orthogonal S


/-- Isotropic subspace -/
def IsIsotropic (S : Submodule (F p) (V n p)) : Prop :=
  S ≤ sym_orth S

/-- The distance of the stabilizer code defined by S -/
noncomputable def code_dist (S : Submodule (F p) (V n p)) : ℕ :=
  sInf {d | ∃ v ∈ sym_orth S, v ∉ S ∧ wt v = d}

/-
Definition of correctable erasure.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Correctable erasure (commutant form) -/
def correctable (S : Submodule (F p) (V n p)) (E : Finset (Fin n)) : Prop :=
  sym_orth S ⊓ V_sub (p:=p) E ≤ S

/-
Distance implies erasure correctability.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

lemma dist_implies_correctable (S : Submodule (F p) (V n p)) (E : Finset (Fin n))
    (h : E.card < code_dist S) : correctable S E := by
      intro v hv;
      have h_weight : ∀ v ∈ sym_orth S ⊓ V_sub E, v∉ S → code_dist S ≤ wt v := by
        exact fun v hv hv' => Nat.sInf_le ⟨ v, hv.1, hv', rfl ⟩;
      have h_weight_le : ∀ v ∈ sym_orth S ⊓ V_sub E, v∉ S → wt v ≤ E.card := by
        intros v hv hv_not_in_S
        have h_support_subset : supp v ⊆ E := by
          exact fun i hi => Classical.not_not.1 fun hi' => by have := hv.2 i hi'; unfold supp at hi; simp_all only [Submodule.mem_inf,
            LinearMap.BilinForm.mem_orthogonal_iff, Prod.forall, and_imp, ne_eq, Set.toFinset_setOf,
            Finset.mem_filter, Finset.mem_univ, not_true_eq_false, or_self, and_false];
        exact Finset.card_le_card h_support_subset;
      exact Classical.not_not.1 fun hv' => not_lt_of_ge ( h_weight v hv hv' ) ( lt_of_le_of_lt ( h_weight_le v hv hv' ) h )

/-
Definition of g(M) with intermediate steps.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Intersection of S and V_M -/
def S_M (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) : Submodule (F p) (V n p) :=
  S ⊓ V_sub (p:=p) M

/-- Intersection of S^\perp and V_M -/
def S_perp_M (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) : Submodule (F p) (V n p) :=
  sym_orth S ⊓ V_sub (p:=p) M

/-- Supportable logical operators count g(M) -/
noncomputable def g (S : Submodule (F p) (V n p)) (M : Finset (Fin n)) : ℕ :=
  Module.finrank (F p) (S_perp_M S M) - Module.finrank (F p) (S_M S M)

/-
Checking FiniteDimensional instances.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

#synth FiniteDimensional (F p) (V_sub (p:=p) (n:=n) ∅)
#synth FiniteDimensional (F p) (Submodule.map (r_E (p:=p) (n:=n) ∅) (⊤ : Submodule (F p) (V n p)))

/-
The kernel of the restriction map r_E is the subspace supported on the complement of E.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Kernel of r_E is V_{E^c} -/
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


/-
Defining complement of E.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Complement of E -/
def E_c (E : Finset (Fin n)) : Finset (Fin n) := Eᶜ

#check E_c

/-
E_c E is the set difference of univ and E.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

lemma E_c_eq (E : Finset (Fin n)) : E_c E = Finset.univ \ E := by
  ext
  simp [E_c]

/-
Dimension of projection of S onto E is dim(S) - dim(S ∩ V_{E^c}).
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Rank-nullity for restriction of S to E -/
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

/-
Symplectic form of v (in V_M) and s is equal to symplectic form of v and r_E M s.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Symplectic form respects restriction -/
lemma sym_form_r_E (M : Finset (Fin n)) (v : V n p) (hv : v ∈ V_sub (p:=p) M) (s : V n p) :
    sym_form v s = sym_form v (r_E M s) := by
      refine' Finset.sum_congr rfl fun i hi => _;
      by_cases hi' : i ∈ M <;> simp_all +decide [ r_E ];
      cases hv i hi' ; simp_all only [zero_mul, sub_self]



def r_E_V (E : Finset (Fin n)) : V n p →ₗ[F p] V n p :=
  (V_sub (p:=p) E).subtype.comp (r_E E)

lemma sym_form_r_E_left (M : Finset (Fin n)) (s v : V n p)
    (hv : v ∈ V_sub (p:=p) M) :
    sym_form (n:=n) (p:=p) ((r_E_V (n:=n) (p:=p) M) s) v
      = sym_form (n:=n) (p:=p) s v := by
  have h_right :
      sym_form (n:=n) (p:=p) v ((r_E_V (n:=n) (p:=p) M) s)
        = sym_form (n:=n) (p:=p) v s := by
    simpa [r_E_V] using (sym_form_r_E (n:=n) (p:=p) M v hv s).symm

  calc
    sym_form ((r_E_V (n:=n) (p:=p) M) s) v
        = - sym_form v ((r_E_V (n:=n) (p:=p) M) s) := by
            simpa using (sym_form_swap (n:=n) (p:=p)
              (u := (r_E_V (n:=n) (p:=p) M) s) (v := v))
    _ = - sym_form v s := by simp [h_right]
    _ = sym_form s v := by
          have := congrArg Neg.neg (sym_form_swap (n:=n) (p:=p) (u := v) (v := s))
          simpa using this

/-
The symplectic form restricted to V_sub M is non-degenerate.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Non-degeneracy on V_sub M -/
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


/-
Intersection of S^\perp with V_M is the same as intersection of (r_M(S))^\perp with V_M.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Restriction map as an endomorphism of V -/




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


/-- Orthogonal intersection lemma -/
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

/-
Checking if S_M and S_perp_M are already defined.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

#check S_M
#check S_perp_M

/-
Definition of restricted symplectic form on V_sub M.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Symplectic bilinear form restricted to `V_sub M`. -/
noncomputable def symB_sub (M : Finset (Fin n)) : LinearMap.BilinForm (F p) (V_sub (p:=p) M) :=
  (symB (n:=n) (p:=p)).comp (V_sub (p:=p) M).subtype (V_sub (p:=p) M).subtype

abbrev sym_form_sub (M : Finset (Fin n)) :
    LinearMap.BilinForm (F p) ↥(V_sub (p:=p) M) :=
  symB_sub (n:=n) (p:=p) M

@[simp] lemma sym_form_sub_apply (M : Finset (Fin n))
    (x y : ↥(V_sub (p:=p) M)) :
    sym_form_sub (n:=n) (p:=p) M x y
      = sym_form (n:=n) (p:=p) (x : V n p) (y : V n p) := rfl

/-
The restricted symplectic form is non-degenerate.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Non-degeneracy of restricted form -/
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

/-
S^\perp \cap V_M is the image of the orthogonal complement of r_M(S) in V_M.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- The intersection S^\perp ∩ V_M corresponds to the orthogonal complement of r_M(S) in V_M -/

lemma orth_inter_eq_orth_sub_image (M : Finset (Fin n)) (S : Submodule (F p) (V n p)) :
    sym_orth S ⊓ V_sub (p:=p) M = ((sym_form_sub (p:=p) M).orthogonal (S.map (r_E M))).map (V_sub (p:=p) M).subtype := by
  classical
  convert orth_inter_eq_orth_map M S using 1;
  ext; simp [sym_form_sub];
  simp +decide [ symB, LinearMap.BilinForm.IsOrtho ];
  simp +decide [ r_E_V, Subtype.ext_iff ];
  grind


/-
The restricted symplectic form is reflexive.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- The restricted symplectic form is reflexive -/
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

/-
Dimension of S^\perp \cap V_M is 2|M| - dim(r_M(S)).
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Dimension of orthogonal intersection -/
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

/-
Expansion of g(M) in terms of dimensions of S and intersections.
-/
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

/-
The complement of the complement is the original set.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

lemma E_c_E_c (M : Finset (Fin n)) : E_c (E_c M) = M := by
  simp [E_c]

/-
The sum of dimensions of S restricted to M and M^c is at most dim(S).
-/
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


/-
Formula for g(M) in terms of dimensions.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

lemma g_formula (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M = (2 * M.card + Module.finrank (F p) (S_M S (E_c M))) - (Module.finrank (F p) S + Module.finrank (F p) (S_M S M)) := by
      convert g_expansion S hS M using 1;
      grind

/-
Helper identity: g(M) + dim(S_M) + dim(S) = 2|M| + dim(S_Mc).
-/
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

/-
Inequality relating dimensions of S, S_M, and S_Mc.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

lemma dim_ineq_aux (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    Module.finrank (F p) S + Module.finrank (F p) (S_M S M) ≤ 2 * M.card + Module.finrank (F p) (S_M S (E_c M)) := by
      linarith [ g_add_dims S hS M ]

/-
The sum of g(M) and g(M^c) is 2n - 2dim(S).
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Cleaning dimension identity -/
lemma cleaning_dimension_identity (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M + g S (E_c M) = 2 * n - 2 * Module.finrank (F p) S := by
      have h1 : g S M + Module.finrank (F p) (S_M S M) + Module.finrank (F p) S = 2 * M.card + Module.finrank (F p) (S_M S (E_c M)) := by
          exact g_add_dims (n:=n) (p:=p) S hS M
      have h2 : g S (E_c M) + Module.finrank (F p) (S_M S (E_c M)) + Module.finrank (F p) S = 2 * (E_c M).card + Module.finrank (F p) (S_M S M) := by
        convert g_add_dims S hS ( E_c M ) using 1;
        rw [ E_c_E_c ];
      unfold E_c at *; simp_all +decide [ Finset.card_compl ] ;
      exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show M.card ≤ n from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] )

/-
Cardinality of M plus cardinality of M^c is n.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

lemma card_add_compl (M : Finset (Fin n)) : M.card + (E_c M).card = n := by
  unfold E_c; simp +decide [ Finset.card_compl ] ;
  exact Nat.add_sub_of_le ( le_trans ( Finset.card_le_univ _ ) ( by norm_num ) )

/-
If M is correctable, g(M) = 0.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

lemma correctable_implies_g_zero (S : Submodule (F p) (V n p)) (M : Finset (Fin n))
    (h : correctable S M) : g S M = 0 := by
      have h_sub : sym_orth S ⊓ V_sub (p:=p) M ≤ S_M S M := by
        exact fun x hx => ⟨ h hx, hx.2 ⟩;
      refine' Nat.sub_eq_zero_of_le _;
      apply_rules [ Submodule.finrank_mono ]

/-
Checking if cleaning_dimension_identity exists.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

#check cleaning_dimension_identity

/-
If M is correctable, then g(M^c) equals 2k.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- If M is correctable, g(M^c) = 2k -/
lemma g_complement_correctable
    (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n))
    (h : correctable S M) :
    g S (E_c M) = 2 * n - 2 * Module.finrank (F p) S := by
  have h_g_M_zero : g S M = 0 :=
    correctable_implies_g_zero (n:=n) (p:=p) S M h
  have h_sum :
      g S M + g S (E_c M) = 2 * n - 2 * Module.finrank (F p) S :=
    cleaning_dimension_identity (n:=n) (p:=p) S hS M
  simpa [h_g_M_zero] using h_sum



/-
Checking if g_complement_correctable is defined.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

#check g_complement_correctable

/-
If B is correctable and disjoint from C, then g(B ∪ C) <= 2|C|.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]



lemma g_le_two_card_C (S : Submodule (F p) (V n p)) (B C : Finset (Fin n))
    (h_disjoint : Disjoint B C) (hB : correctable S B) :
    g S (B ∪ C) ≤ 2 * C.card := by
      have h_g_def : g S (B ∪ C) = Module.finrank (F p) (S_perp_M S (B ∪ C)) - Module.finrank (F p) (S_M S (B ∪ C)) := by
        rfl;
      have h_S_perp_M_subset : S_perp_M S (B ∪ C) ≤ V_sub (p:=p) (B ∪ C) := by
        exact inf_le_right;

      set U : Submodule (F p) (V n p) := S_perp_M S (B ∪ C);

      set r_C : U →ₗ[F p] V_sub (p:=p) C := (r_E C).comp (Submodule.subtype U);
      have h_kernel_r_C : LinearMap.ker r_C = Submodule.comap (Submodule.subtype U) (V_sub (p:=p) B) := by
        ext v
        simp [r_C, r_E];
        apply Iff.intro
        intro h_zero
        have h_support : ∀ i, i ∉ B → (v : V n p).1 i = 0 ∧ (v : V n p).2 i = 0 := by
          intro i hi; specialize h_S_perp_M_subset v.2; simp_all +decide [ V_sub ] ;
          by_cases hi' : i ∈ C <;> simp_all +decide [ Subtype.ext_iff ];
          exact ⟨ by simpa [ hi' ] using congr_fun h_zero.1 i, by simpa [ hi' ] using congr_fun h_zero.2 i ⟩
        exact (by
        exact fun i hi => by specialize h_support i hi; simp_all only [Submodule.mk_eq_zero, Prod.mk_eq_zero, and_self,
          U];)
        intro h_support
        have h_zero : ∀ i ∈ C, (v : V n p).1 i = 0 ∧ (v : V n p).2 i = 0 := by
          exact fun i hi => h_support i ( Finset.disjoint_right.mp h_disjoint hi )
        exact (by
        ext i; simp_all only [ite_self, ZeroMemClass.coe_zero, Prod.fst_zero, Pi.zero_apply, U];
        by_cases hi : i ∈ C <;> simp +decide [ hi, h_zero ])

      have h_S_perp_B_subset_S : Submodule.comap (Submodule.subtype U) (V_sub (p:=p) B) ≤ Submodule.comap (Submodule.subtype U) S := by
        intro x hx; exact (by
        have := hB ( show x.1 ∈ sym_orth S ⊓ V_sub B from ?_ ) ; simp_all only [Submodule.mem_comap,
          Submodule.subtype_apply, U, r_C];
        exact ⟨ x.2.1, hx ⟩);
      have h_dim_U_le : Module.finrank (F p) U ≤ Module.finrank (F p) (LinearMap.range r_C) + Module.finrank (F p) (Submodule.comap (Submodule.subtype U) S) := by
        have := LinearMap.finrank_range_add_finrank_ker r_C;
        rw [ ← this ];
        exact add_le_add_left ( Submodule.finrank_mono <| h_kernel_r_C ▸ h_S_perp_B_subset_S ) _;
      have h_dim_r_C_U_le : Module.finrank (F p) (LinearMap.range r_C) ≤ 2 * C.card := by
        exact le_trans ( Submodule.finrank_le _ ) ( by erw [ dim_V_sub ] );
      have h_dim_S_inter_V_B_union_C_le : Module.finrank (F p) (Submodule.comap (Submodule.subtype U) S) ≤ Module.finrank (F p) (S_M S (B ∪ C)) := by
        rw [ ← Submodule.finrank_map_subtype_eq ];
        refine' Submodule.finrank_mono _;
        simp +zetaDelta at *;
        exact fun x hx => ⟨ hx.2, h_S_perp_M_subset hx.1 ⟩;
      exact h_g_def.symm ▸ Nat.sub_le_of_le_add ( by linarith )

/-
Definition of the number of logical qudits k.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Number of logical qudits k -/
def code_k (S : Submodule (F p) (V n p)) : ℕ := n - Module.finrank (F p) S

/-
If A and B are disjoint correctable sets, then k <= |C| where C is the complement of A U B.
-/
variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Lemma 5: Two disjoint correctable sets bound logical dimension -/
lemma two_disjoint_correctable_sets_bound_logical_dimension (S : Submodule (F p) (V n p)) (hS : IsIsotropic S)
    (A B : Finset (Fin n)) (h_disjoint : Disjoint A B)
    (hA : correctable S A) (hB : correctable S B) :
    code_k S ≤ (Finset.univ \ (A ∪ B)).card := by
      have h_g_Ac : g S (Finset.univ \ A) = 2 * (n - Module.finrank (F p) S) := by
        convert g_complement_correctable S hS A hA using 1;
        rw [ Nat.mul_sub_left_distrib ];
      have h_g_BC : g S (B ∪ (Finset.univ \ (A ∪ B))) ≤ 2 * (Finset.univ \ (A ∪ B)).card := by
        apply g_le_two_card_C;
        · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp hx₂ |>.2 ( Finset.mem_union_right _ hx₁ );
        · assumption;
      have h_BC_eq_Ac : B ∪ (Finset.univ \ (A ∪ B)) = Finset.univ \ A := by
        ext x; by_cases hx : x ∈ A <;> by_cases hx' : x ∈ B <;> simp +decide [ hx, hx' ] ;
        exact Finset.disjoint_left.mp h_disjoint hx hx';
      unfold code_k; simp_all only [Nat.ofNat_pos, mul_le_mul_iff_right₀, tsub_le_iff_right];


section SingletonHelpers

variable {n : ℕ} {p : ℕ} [Fact p.Prime]

@[simp] lemma V_sub_univ_eq_top :
    V_sub (n:=n) (p:=p) (Finset.univ : Finset (Fin n))
      = (⊤ : Submodule (F p) (V n p)) := by
  classical
  ext v
  constructor
  · intro _; trivial
  · intro _
    intro i hi
    exact (False.elim (hi (Finset.mem_univ i)))


lemma finrank_V :
    Module.finrank (F p) (V n p) = 2 * n := by
  classical
  have h :=
    dim_V_sub (n:=n) (p:=p) (C := (Finset.univ : Finset (Fin n)))

  have h' :
      Module.finrank (F p)
          ((⊤ : Submodule (F p) (V n p)) : Type _)
        = 2 * n := by
    have h_top : V_sub (p:=p) (Finset.univ : Finset (Fin n)) = (⊤ : Submodule (F p) (V n p)) := by
      exact V_sub_univ_eq_top;
    rw [h_top] at h; exact h.trans (by simp)
  have ht :
      Module.finrank (F p)
          ((⊤ : Submodule (F p) (V n p)) : Type _)
        = Module.finrank (F p) (V n p) := by
    simpa using
      (Submodule.finrank_top : Module.finrank (F p)
          ((⊤ : Submodule (F p) (V n p)) : Type _)
        = Module.finrank (F p) (V n p))
  exact ht.symm.trans h'


  lemma symB_nondegenerate :
    (symB (n:=n) (p:=p)).Nondegenerate := by
  intro u hu
  apply sym_form_nondegenerate (n:=n) (p:=p) u
  intro v
  simpa [symB_apply] using hu v

lemma symB_isRefl :
    (symB (n:=n) (p:=p)).IsRefl := by
  intro v w h
  have h' : sym_form (n:=n) (p:=p) v w = 0 := by
    simpa [symB_apply] using h
  have : sym_form (n:=n) (p:=p) w v = 0 := by
    simpa [sym_form_swap (n:=n) (p:=p) w v, h']
  simpa [symB_apply] using this

lemma finrank_sym_orth (S : Submodule (F p) (V n p)) :
    Module.finrank (F p) (sym_orth (n:=n) (p:=p) S)
      = 2 * n - Module.finrank (F p) S := by
  classical
  have h :=
    LinearMap.BilinForm.finrank_orthogonal
      (B := symB (n:=n) (p:=p))
      (symB_nondegenerate (n:=n) (p:=p))
      (symB_isRefl (n:=n) (p:=p))
      S
  simpa [sym_orth, finrank_V (n:=n) (p:=p)] using h



lemma finrank_le_n_of_isotropic (S : Submodule (F p) (V n p)) (hS : IsIsotropic (n:=n) (p:=p) S) :
    Module.finrank (F p) S ≤ n := by
  classical
  have hmono :
      Module.finrank (F p) S ≤ Module.finrank (F p) (sym_orth (n:=n) (p:=p) S) :=
    Submodule.finrank_mono hS
  have hineq :
      Module.finrank (F p) S ≤ 2 * n - Module.finrank (F p) S := by
    simpa [finrank_sym_orth (n:=n) (p:=p) S] using hmono
  have a_le_2n :
      Module.finrank (F p) S ≤ 2 * n := by
    have : Module.finrank (F p) S ≤ Module.finrank (F p) (V n p) := by
      simpa using (Submodule.finrank_le (R := F p) (M := V n p) S)
    simpa [finrank_V (n:=n) (p:=p)] using this
  have h2 : 2 * Module.finrank (F p) S ≤ 2 * n := by
    have hadd :
        Module.finrank (F p) S + Module.finrank (F p) S ≤ 2 * n := by
      exact (Nat.le_sub_iff_add_le a_le_2n).1 hineq
    simpa [two_mul] using hadd
  exact Nat.le_of_mul_le_mul_left h2 (by decide : 0 < 2)



/-- Any vector in `V n p` has weight at most `n`. -/
lemma wt_le_n (v : V n p) : wt (n:=n) (p:=p) v ≤ n := by
  classical
  unfold wt
  have hs : supp (n:=n) (p:=p) v ⊆ (Finset.univ : Finset (Fin n)) := by
    intro i hi
    simpa using (Finset.mem_univ i)
  have hcard :
      (supp (n:=n) (p:=p) v).card ≤ (Finset.univ : Finset (Fin n)).card :=
    Finset.card_mono hs
  simpa [Finset.card_univ] using hcard


/-- `code_dist S ≤ n` since all weights are bounded by `n`. -/
lemma code_dist_le_n (S : Submodule (F p) (V n p)) :
    code_dist (n:=n) (p:=p) S ≤ n := by
  classical
  let D : Set ℕ :=
    { d | ∃ v ∈ sym_orth (n:=n) (p:=p) S, v ∉ S ∧ wt (n:=n) (p:=p) v = d }

  unfold code_dist
  change sInf D ≤ n

  by_cases hD : D = ∅
  ·
    simpa [hD] using (Nat.zero_le n)
  ·
    have hDne : D.Nonempty := Set.nonempty_iff_ne_empty.2 hD
    rcases hDne with ⟨d0, hd0mem⟩
    rcases hd0mem with ⟨v, hvS, hvnotS, hwt⟩
    have hd0 : d0 ∈ D := ⟨v, hvS, hvnotS, hwt⟩

    have hBdd : BddBelow D := ⟨0, by
      intro d hd
      exact Nat.zero_le d⟩

    have hdist_le : sInf D ≤ d0 := by
      exact csInf_le hBdd hd0

    have hd0_le : d0 ≤ n := by
      have : wt (n:=n) (p:=p) v ≤ n := wt_le_n (n:=n) (p:=p) v
      simpa [hwt] using this

    exact le_trans hdist_le hd0_le




lemma code_dist_eq_zero_of_code_k_eq_zero
    (S : Submodule (F p) (V n p))
    (hS : IsIsotropic (n:=n) (p:=p) S)
    (hk : code_k (n:=n) (p:=p) S = 0) :
    code_dist (n:=n) (p:=p) S = 0 := by
  classical
  have hfin_le_n : Module.finrank (F p) S ≤ n :=
    finrank_le_n_of_isotropic (n:=n) (p:=p) S hS
  have hk' : n - Module.finrank (F p) S = 0 := by
    simpa [code_k] using hk
  have hn_le_fin : n ≤ Module.finrank (F p) S :=
    (Nat.sub_eq_zero_iff_le).1 hk'
  have hfin_eq : Module.finrank (F p) S = n :=
    Nat.le_antisymm hfin_le_n hn_le_fin

  have hfin_orth :
      Module.finrank (F p) (sym_orth (n:=n) (p:=p) S)
        = Module.finrank (F p) S := by
    calc
      Module.finrank (F p) (sym_orth (n:=n) (p:=p) S)
          = 2 * n - Module.finrank (F p) S := by
            simpa using finrank_sym_orth (n:=n) (p:=p) S
      _ = 2 * n - n := by simp [hfin_eq]
      _ = n := by
            simpa [two_mul] using (Nat.add_sub_cancel_left n n)
      _ = Module.finrank (F p) S := by simp [hfin_eq]

  have hEq : S = sym_orth (n:=n) (p:=p) S := by
    apply Submodule.eq_of_le_of_finrank_eq hS
    simpa using hfin_orth.symm

  unfold code_dist
  rw [← hEq]

  have hEmpty :
      {d : ℕ | ∃ v ∈ S, v ∉ S ∧ wt (n:=n) (p:=p) v = d} = (∅ : Set ℕ) := by
    ext d
    constructor
    · rintro ⟨v, hvS, hvnotS, -⟩
      exact (hvnotS hvS).elim
    · intro hd
      cases hd

  rw [hEmpty]
  simp




end SingletonHelpers




section QuantumSingleton

variable {n : ℕ} {p : ℕ} [Fact p.Prime]

/-- Choose disjoint finsets `A,B` of size `t` inside `Fin n`, assuming `2t ≤ n`. -/
lemma exists_disjoint_finsets_card (t : ℕ) (h : 2 * t ≤ n) :
    ∃ A B : Finset (Fin n), Disjoint A B ∧ A.card = t ∧ B.card = t := by
  classical
  let U : Finset (Fin n) := Finset.univ
  have hU : U.card = n := by simp [U]

  have hsum : t + t ≤ U.card := by
    simpa [hU, two_mul] using h
  have htU : t ≤ U.card := le_trans (Nat.le_add_left t t) hsum

  obtain ⟨A, hA_sub, hA_card⟩ := Finset.exists_subset_card_eq htU

  have hcard_sdiff : (U \ A).card = U.card - A.card := by
    have h' : (U \ A).card = U.card - (A ∩ U).card := by
      simpa using (Finset.card_sdiff (s := A) (t := U))
    simpa [Finset.inter_eq_left.2 hA_sub] using h'

  have htUdiff : t ≤ (U \ A).card := by
    have ht : t ≤ U.card - t :=
      (Nat.le_sub_iff_add_le htU).2 hsum
    simpa [hcard_sdiff, hA_card] using ht

  obtain ⟨B, hB_sub, hB_card⟩ := Finset.exists_subset_card_eq htUdiff

  have hdisj : Disjoint A B := by
    refine Finset.disjoint_left.2 ?_
    intro x hxA hxB
    have hxBUA : x ∈ U \ A := hB_sub hxB
    exact (Finset.mem_sdiff.1 hxBUA).2 hxA

  exact ⟨A, B, hdisj, hA_card, hB_card⟩



/-- Quantum Singleton bound: `code_k S + 2*(code_dist S - 1) ≤ n`. -/
theorem quantum_singleton_bound
    (S : Submodule (F p) (V n p))
    (hS : IsIsotropic (n:=n) (p:=p) S) :
    code_k (n:=n) (p:=p) S + 2 * (code_dist (n:=n) (p:=p) S - 1) ≤ n := by
  classical

  -- Case split on `code_dist S`.
  cases hcd : code_dist (n:=n) (p:=p) S with
  | zero =>
      have hk_le : code_k (n:=n) (p:=p) S ≤ n := by
        simpa [code_k] using (Nat.sub_le n (Module.finrank (F p) S))
      simpa [hcd] using hk_le

  | succ d' =>
      have hd_pred : code_dist (n:=n) (p:=p) S - 1 = d' := by
        simpa [hcd] using (Nat.succ_sub_one d')

      have hd'_lt : d' < code_dist (n:=n) (p:=p) S := by
        simpa [hcd] using (Nat.lt_succ_self d')

      have h2t : 2 * d' ≤ n := by
        by_contra hnot
        have hn : n < 2 * d' := Nat.lt_of_not_ge hnot

        have hd_le_n : code_dist (n:=n) (p:=p) S ≤ n :=
          code_dist_le_n (n:=n) (p:=p) S
        have hsucc_le : Nat.succ d' ≤ n := by simpa [hcd] using hd_le_n
        have hd'_le_n : d' ≤ n := Nat.le_of_lt (Nat.lt_of_succ_le hsucc_le)

        have hdU : d' ≤ (Finset.univ : Finset (Fin n)).card := by
          simpa [Finset.card_univ] using hd'_le_n
        obtain ⟨A, hA_sub, hA_card⟩ := Finset.exists_subset_card_eq hdU

        let B : Finset (Fin n) := (Finset.univ : Finset (Fin n)) \ A

        have hdisj : Disjoint A B := by
          refine Finset.disjoint_left.2 ?_
          intro x hxA hxB
          have hxBUA : x ∈ (Finset.univ : Finset (Fin n)) \ A := by simpa [B] using hxB
          exact (Finset.mem_sdiff.1 hxBUA).2 hxA

        -- Compute `B.card = n - d'`.
        have hB_card : B.card = n - d' := by
          have h' :
              ((Finset.univ : Finset (Fin n)) \ A).card
                =
              (Finset.univ : Finset (Fin n)).card - (A ∩ (Finset.univ : Finset (Fin n))).card := by
            simpa using (Finset.card_sdiff (s := A) (t := (Finset.univ : Finset (Fin n))))
          simpa [B, hA_card, Finset.card_univ, Finset.inter_eq_left.2 hA_sub] using h'

        have hA_corr : correctable (n:=n) (p:=p) S A := by
          apply dist_implies_correctable (n:=n) (p:=p) S A
          simpa [hA_card] using hd'_lt

        have hB_corr : correctable (n:=n) (p:=p) S B := by
          apply dist_implies_correctable (n:=n) (p:=p) S B
          have hle : n - d' ≤ d' := by
            apply (Nat.sub_le_iff_le_add).2
            exact Nat.le_of_lt (by simpa [two_mul] using hn)
          have hlt : n - d' < Nat.succ d' := Nat.lt_succ_of_le hle
          simpa [hB_card, hcd] using hlt

        have hk_le :
            code_k (n:=n) (p:=p) S
              ≤ ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card :=
          two_disjoint_correctable_sets_bound_logical_dimension
            (n:=n) (p:=p) S hS A B hdisj hA_corr hB_corr

        have hAU : A ∪ B = (Finset.univ : Finset (Fin n)) := by
          ext x
          simp [B]

        have hcomp0 : ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card = 0 := by
          simpa [hAU]

        have hk_le0 : code_k (n:=n) (p:=p) S ≤ 0 := by
          simpa [hcomp0] using hk_le

        have hk0 : code_k (n:=n) (p:=p) S = 0 :=
          Nat.eq_zero_of_le_zero hk_le0

        have hd0 : code_dist (n:=n) (p:=p) S = 0 :=
          code_dist_eq_zero_of_code_k_eq_zero (n:=n) (p:=p) S hS hk0

        have : Nat.succ d' = 0 := by
          simpa [hcd] using hd0
        exact (Nat.succ_ne_zero d') this

      obtain ⟨A, B, hdisj, hA_card, hB_card⟩ :=
        exists_disjoint_finsets_card (n:=n) d' h2t

      have hA_corr : correctable (n:=n) (p:=p) S A := by
        apply dist_implies_correctable (n:=n) (p:=p) S A
        simpa [hA_card] using hd'_lt

      have hB_corr : correctable (n:=n) (p:=p) S B := by
        apply dist_implies_correctable (n:=n) (p:=p) S B
        simpa [hB_card] using hd'_lt

      have hk_leC :
          code_k (n:=n) (p:=p) S
            ≤ ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card :=
        two_disjoint_correctable_sets_bound_logical_dimension
          (n:=n) (p:=p) S hS A B hdisj hA_corr hB_corr

      have hC :
          ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card = n - 2 * d' := by
        have hsdiff :
            ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card
              =
            (Finset.univ : Finset (Fin n)).card - ((A ∪ B) ∩ (Finset.univ : Finset (Fin n))).card := by
          simpa using
            (Finset.card_sdiff (s := (A ∪ B)) (t := (Finset.univ : Finset (Fin n))))
        have hinter :
            ((A ∪ B) ∩ (Finset.univ : Finset (Fin n))) = (A ∪ B) :=
          Finset.inter_eq_left.2 (Finset.subset_univ _)
        have hsdiff' :
            ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card
              =
            (Finset.univ : Finset (Fin n)).card - (A ∪ B).card := by
          simpa [hinter] using hsdiff
        have hunion : (A ∪ B).card = 2 * d' := by
          calc
            (A ∪ B).card = A.card + B.card := Finset.card_union_of_disjoint hdisj
            _ = d' + d' := by simp [hA_card, hB_card]
            _ = 2 * d' := by simpa [two_mul]
        calc
          ((Finset.univ : Finset (Fin n)) \ (A ∪ B)).card
              =
            (Finset.univ : Finset (Fin n)).card - (A ∪ B).card := hsdiff'
          _ = n - 2 * d' := by simp [Finset.card_univ, hunion]

      have hk_le_sub : code_k (n:=n) (p:=p) S ≤ n - 2 * d' := by
        simpa [hC] using hk_leC

      have hmain : code_k (n:=n) (p:=p) S + 2 * d' ≤ n := by
        calc
          code_k (n:=n) (p:=p) S + 2 * d'
              ≤ (n - 2 * d') + 2 * d' := by
                  exact Nat.add_le_add_right hk_le_sub _
          _ = n := by
                  exact Nat.sub_add_cancel h2t

      simpa [hd_pred] using hmain


end QuantumSingleton
