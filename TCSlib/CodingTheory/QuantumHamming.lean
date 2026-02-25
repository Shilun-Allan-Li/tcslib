import Mathlib


set_option linter.mathlibStandardSet false

open scoped BigOperators

open scoped Real

open scoped Nat

open scoped Classical

open scoped Pointwise

set_option maxHeartbeats 0

set_option maxRecDepth 4000

set_option synthInstance.maxHeartbeats 20000

set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false

set_option autoImplicit false

noncomputable section

open Complex Matrix

/-
Pauli basis {I,X,Y,Z} and concrete matrices.
-/
inductive PauliBasis
| I | X | Y | Z
deriving DecidableEq, Fintype, Inhabited

def sigmaI : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, 1]

def sigmaX : Matrix (Fin 2) (Fin 2) ℂ := !![0, 1; 1, 0]

def sigmaY : Matrix (Fin 2) (Fin 2) ℂ := !![0, -I; I, 0]

def sigmaZ : Matrix (Fin 2) (Fin 2) ℂ := !![1, 0; 0, -1]

def PauliBasis.toMatrix : PauliBasis → Matrix (Fin 2) (Fin 2) ℂ
| PauliBasis.I => sigmaI
| PauliBasis.X => sigmaX
| PauliBasis.Y => sigmaY
| PauliBasis.Z => sigmaZ


def PauliString (n : ℕ) := Fin n → PauliBasis

instance (n : ℕ) : Fintype (PauliString n) := inferInstanceAs (Fintype (Fin n → PauliBasis))

def support {n : ℕ} (p : PauliString n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => p i ≠ PauliBasis.I)

def weight {n : ℕ} (p : PauliString n) : ℕ :=
  (support p).card

def pauliMatrix {n : ℕ} (p : PauliString n) :
    Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ :=
  fun i j => ∏ k, (p k).toMatrix (i k) (j k)

/-
Pauli errors of weight ≤ t.
-/
def PauliErrorsLe (n t : ℕ) : Finset (PauliString n) :=
  Finset.filter (fun p => weight p ≤ t) Finset.univ

/-
Counting Paulis: canonical “choose support then assign X/Y/Z” approach.
We introduce a 3-element type for non-identity Paulis.
-/
inductive PauliNZ | X | Y | Z
deriving DecidableEq, Fintype, Inhabited

def PauliNZ.toBasis : PauliNZ → PauliBasis
| .X => .X
| .Y => .Y
| .Z => .Z

lemma PauliNZ.toBasis_ne_I : ∀ a : PauliNZ, a.toBasis ≠ PauliBasis.I := by
  intro a; cases a <;> simp [PauliNZ.toBasis]


def mkWithSupport {n : ℕ} (S : Finset (Fin n)) (f : S → PauliNZ) : PauliString n :=
  fun i => if h : i ∈ S then (f ⟨i, h⟩).toBasis else PauliBasis.I

lemma support_mkWithSupport {n : ℕ} (S : Finset (Fin n)) (f : S → PauliNZ) :
    support (mkWithSupport S f) = S := by
  classical
  ext i
  simp [support, mkWithSupport, PauliNZ.toBasis_ne_I]


def pauliStringsExactSupport {n : ℕ} (S : Finset (Fin n)) : Finset (PauliString n) :=
  Finset.filter (fun p => support p = S) Finset.univ


lemma card_pauliStringsExactSupport {n : ℕ} (S : Finset (Fin n)) :
    (pauliStringsExactSupport (n:=n) S).card = 3 ^ S.card := by
  classical
  /-
  Standard proof outline:
  - show the subtype `{p // support p = S}` is in bijection with `S → PauliNZ` via `mkWithSupport`
  - `Fintype.card (S → PauliNZ) = 3^(S.card)`
  - translate to finset-card
  -/
  rw [ show pauliStringsExactSupport S = Finset.image ( fun f : S → PauliNZ => mkWithSupport S f ) ( Finset.univ ) from by
  ext p
  simp [pauliStringsExactSupport, mkWithSupport]
  constructor <;> intro hp
  · have h_non_id : ∀ i ∈ S, p i ≠ PauliBasis.I := by
      simp +decide [← hp, support]
    use fun i =>
      if p i = PauliBasis.X then PauliNZ.X
      else if p i = PauliBasis.Y then PauliNZ.Y
      else PauliNZ.Z
    funext i
    by_cases hi : i ∈ S <;> simp_all +decide [mkWithSupport]
    · cases hpi : p i <;> aesop
    · unfold support at hp
      subst hp
      simp_all only [ne_eq, Finset.mem_filter, Finset.mem_univ, true_and, not_false_eq_true, implies_true,
        Decidable.not_not]
  · obtain ⟨a, rfl⟩ := hp
    exact support_mkWithSupport S a ];
  · rw [ Finset.card_image_of_injective, Finset.card_univ ] ; aesop;
    intro f g hfg
    have h_eq : ∀ i : S, f i = g i := by
      intro i; replace hfg := congr_fun hfg i; simp_all +decide [ mkWithSupport ] ;
      rcases f_i : f i with ( _ | _ | _ ) <;> rcases g_i : g i with ( _ | _ | _ ) <;> simp_all +decide [ PauliNZ.toBasis ]
    exact funext h_eq;


/-- Clean Quantum Hamming counting identity. -/
theorem card_pauliErrorsLe (n t : ℕ) :
    (PauliErrorsLe n t).card = ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j := by
  classical
  /-
   proof outline:
  - partition by `j = weight p`
  - partition by exact support `S` with `S.card = j`
  - count supports: `card (powersetCard j univ) = n.choose j`
  - each support contributes `3^j` by `card_pauliStringsExactSupport`
  -/
  have h_union : PauliErrorsLe n t = Finset.biUnion (Finset.range (t + 1)) (fun j => Finset.biUnion (Finset.powersetCard j (Finset.univ : Finset (Fin n))) (fun S => pauliStringsExactSupport S)) := by
    ext p; simp [PauliErrorsLe, pauliStringsExactSupport];
    exact Nat.lt_succ_iff.symm;
  rw [ h_union, Finset.card_biUnion, Finset.sum_congr rfl ];
  · intro j hj; rw [ Finset.card_biUnion ];
    · rw [ Finset.sum_congr rfl fun x hx => card_pauliStringsExactSupport x ];
      rw [ Finset.sum_congr rfl fun x hx => by rw [ Finset.mem_powersetCard.mp hx |>.2 ] ] ; simp +decide [ Finset.card_univ ];
    · intro S hS T hT hST; simp_all +decide [ Finset.disjoint_left, pauliStringsExactSupport ] ;
  · intros j hj k hk hjk; simp_all +decide [ Finset.disjoint_left ] ;
    unfold pauliStringsExactSupport;
    intro a x a_1 a_2 x_1 a_3
    subst a_1 a_3
    simp_all only [Finset.mem_filter, Finset.mem_univ, true_and]
    subst a_2
    apply Aesop.BuiltinRules.not_intro
    intro a_1
    subst a_1
    simp_all only [not_true_eq_false];


abbrev Hn (n : ℕ) := EuclideanSpace ℂ (Fin n → Fin 2)

def Code (n : ℕ) := Submodule ℂ (Hn n)

noncomputable def pauliOp {n : ℕ} (p : PauliString n) : Hn n →ₗ[ℂ] Hn n :=
  Matrix.toLin' (pauliMatrix p)

noncomputable def pauliOpAdjoint {n : ℕ} (p : PauliString n) : Hn n →ₗ[ℂ] Hn n :=
  Matrix.toLin' (pauliMatrix p).conjTranspose


instance (n : ℕ) (C : Submodule ℂ (Hn n)) : FiniteDimensional ℂ (↥C) :=
  FiniteDimensional.finiteDimensional_submodule C

noncomputable def codeProj {n : ℕ} (C : Submodule ℂ (Hn n)) : Hn n →ₗ[ℂ] Hn n :=
  (C.subtypeL.comp (Submodule.orthogonalProjection C)).toLinearMap

@[simp] lemma codeProj_apply {n : ℕ} (C : Submodule ℂ (Hn n)) (x : Hn n) :
    codeProj C x = (Submodule.orthogonalProjection C x : Hn n) := by
  simp [codeProj]

lemma codeProj_mem {n : ℕ} (C : Submodule ℂ (Hn n)) (x : Hn n) :
    codeProj C x ∈ C := by
  -- `orthogonalProjection C x : C`
  simpa [codeProj_apply] using (Submodule.coe_mem C (Submodule.orthogonalProjection C x))

lemma codeProj_eq_self_of_mem {n : ℕ} {C : Submodule ℂ (Hn n)} {x : Hn n} (hx : x ∈ C) :
    codeProj C x = x := by

  have h_proj : ∀ x : Hn n, x ∈ C → Submodule.orthogonalProjection C x = x := by
    intros x hx
    apply Submodule.starProjection_eq_self_iff.mpr hx;
  apply h_proj; assumption

lemma codeProj_idempotent {n : ℕ} (C : Submodule ℂ (Hn n)) (x : Hn n) :
    codeProj C (codeProj C x) = codeProj C x := by
  apply codeProj_eq_self_of_mem (C:=C)
  exact codeProj_mem C x

/-
Knill–Laflamme and (a strong) nondegeneracy condition.
-/
def KnillLaflamme (n : ℕ) (C : Submodule ℂ (Hn n)) (t : ℕ) : Prop :=
  ∀ E F : PauliString n, weight E ≤ t → weight F ≤ t →
    ∃ α : ℂ,
      (codeProj C).comp ((pauliOpAdjoint E).comp ((pauliOp F).comp (codeProj C))) =
      α • (codeProj C)

def IsNondegenerate (n : ℕ) (C : Submodule ℂ (Hn n)) (t : ℕ) : Prop :=
  KnillLaflamme n C t ∧
  ∀ E F : PauliString n, weight E ≤ t → weight F ≤ t → E ≠ F →
    (codeProj C).comp ((pauliOpAdjoint E).comp ((pauliOp F).comp (codeProj C))) = 0

noncomputable def ErrorSphere (n t : ℕ) (C : Submodule ℂ (Hn n)) : Submodule ℂ (Hn n) :=
  (PauliErrorsLe n t).sup (fun E => C.map (pauliOp E))

lemma error_subspaces_orthogonal {n t : ℕ} {C : Submodule ℂ (Hn n)}
    (h_nondeg : IsNondegenerate n C t)
    (E F : PauliString n) (hE : weight E ≤ t) (hF : weight F ≤ t) (h_neq : E ≠ F) :
    Submodule.IsOrtho (C.map (pauliOp E)) (C.map (pauliOp F)) := by

  have h_ortho : ∀ x y : Hn n, x ∈ C → y ∈ C → (pauliOp E x) ⬝ᵥ (star (pauliOp F y)) = 0 := by
    have := h_nondeg.2 E F hE hF h_neq;
    intro x y hx hy; replace this := congr_arg ( fun f => f y ) this; simp_all +decide [ funext_iff, LinearMap.ext_iff ] ;
    have h_adj : (pauliOp E x) ⬝ᵥ (star (pauliOp F y)) = x ⬝ᵥ (star (pauliOpAdjoint E (pauliOp F y))) := by
      have h_adj : ∀ (A : Matrix (Fin n → Fin 2) (Fin n → Fin 2) ℂ) (x y : EuclideanSpace ℂ (Fin n → Fin 2)), (A.mulVec x) ⬝ᵥ (star y) = x ⬝ᵥ (star (A.conjTranspose.mulVec y)) := by
        simp +decide [ Matrix.mulVec, dotProduct, Finset.mul_sum _ _ _, mul_assoc, mul_comm, mul_left_comm ];
        exact fun A x y => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring );
      convert h_adj ( pauliMatrix E ) x ( pauliOp F y ) using 1;
    have h_adj_zero : (pauliOpAdjoint E (pauliOp F y)) = (pauliOpAdjoint E (pauliOp F (codeProj C y))) := by
      rw [ codeProj_eq_self_of_mem hy ];
    have h_adj_zero : ∀ x y : Hn n, x ∈ C → (x ⬝ᵥ (star (codeProj C y))) = (x ⬝ᵥ (star y)) := by
      intro x y hx; rw [ codeProj_apply ] ; simp +decide [ hx, dotProduct ] ;
      have h_adj_zero : ∀ x y : Hn n, x ∈ C → (x ⬝ᵥ (star (Submodule.starProjection C y))) = (x ⬝ᵥ (star y)) := by
        intro x y hx
        have h_ortho : ∀ z ∈ Cᗮ, (x ⬝ᵥ (star z)) = 0 := by
          intro z hz; specialize hz x hx; simp_all +decide [ dotProduct, Finset.sum_eq_zero_iff_of_nonneg, sq_nonneg ] ;
          simpa [ mul_comm ] using congr_arg Star.star hz
        have h_ortho : (x ⬝ᵥ (star (Submodule.starProjection C y))) = (x ⬝ᵥ (star y)) - (x ⬝ᵥ (star (y - Submodule.starProjection C y))) := by
          simp +decide [ mul_sub ];
        have h_ortho : y - Submodule.starProjection C y ∈ Cᗮ := by
          exact Submodule.sub_orthogonalProjection_mem_orthogonal y;
        grind;
      exact h_adj_zero x y hx;
    specialize h_adj_zero x ( ( pauliOpAdjoint E ) ( ( pauliOp F ) ( codeProj C y ) ) ) hx; simp_all only [codeProj_apply,
      Submodule.coe_orthogonalProjection_apply, star_zero, dotProduct_zero];
  intro x hx y hy;
  simp_all only [ne_eq, Submodule.mem_map]
  obtain ⟨w, h⟩ := hx
  obtain ⟨w_1, h_1⟩ := hy
  obtain ⟨left, right⟩ := h
  obtain ⟨left_1, right_1⟩ := h_1
  subst right right_1
  apply h_ortho
  · simp_all only
  · simp_all only;


  /-
   proof in hsort:
  - show the family `(C.map (pauliOp E))` is pairwise disjoint (inf = ⊥) via orthogonality
  - use finrank of supremum over pairwise disjoint finite family
  - show each `pauliOp E` restricts to a linear equiv on `C` (invertible/unitary), hence
    `finrank (C.map (pauliOp E)) = finrank C`
  -/
lemma error_sphere_dimension {n t : ℕ} {C : Submodule ℂ (Hn n)}
    (h_nondeg : IsNondegenerate n C t) :
    Module.finrank ℂ (ErrorSphere n t C) =
    (PauliErrorsLe n t).card * Module.finrank ℂ C := by
  /-
  proof strat:
  - show the family `(C.map (pauliOp E))` is pairwise disjoint (inf = ⊥) via orthogonality
  - use finrank of supremum over pairwise disjoint finite family
  - show each `pauliOp E` restricts to a linear equiv on `C` (invertible/unitary), hence
    `finrank (C.map (pauliOp E)) = finrank C`
  -/
  have h_dim_sum :
      ∀ (S : Finset (PauliString n)),
        (∀ E ∈ S, weight E ≤ t) →
          Module.finrank ℂ (↥(Finset.sup S (fun E => C.map (pauliOp E))))
            = Finset.card S * Module.finrank ℂ C := by
    intro S hS
    induction' S using Finset.induction with E S hES ih
    · simp +decide [Submodule.eq_bot_iff]
    · have h_orthogonal :
          Submodule.IsOrtho (C.map (pauliOp E))
            (Finset.sup S (fun E => C.map (pauliOp E))) := by
        have h_orthogonal :
            ∀ F ∈ S, Submodule.IsOrtho (C.map (pauliOp E)) (C.map (pauliOp F)) := by
          intro F hF
          apply error_subspaces_orthogonal h_nondeg E F
            (hS E (Finset.mem_insert_self E S))
            (hS F (Finset.mem_insert_of_mem hF))
          simp_all only [Finset.mem_insert, or_true, implies_true, forall_const, forall_eq_or_imp, ne_eq]
          obtain ⟨left, right⟩ := hS
          apply Aesop.BuiltinRules.not_intro
          intro a
          subst a
          simp_all only [not_true_eq_false]
        have h_orthogonal_sup :
            ∀ (T : Finset (PauliString n)),
              (∀ F ∈ T, Submodule.IsOrtho (C.map (pauliOp E)) (C.map (pauliOp F))) →
              Submodule.IsOrtho (C.map (pauliOp E))
                (Finset.sup T (fun F => C.map (pauliOp F))) := by
          intro T hT
          induction T using Finset.induction <;> aesop?
        exact h_orthogonal_sup S h_orthogonal

      have h_dim_sum :
          Module.finrank ℂ (↥(C.map (pauliOp E) ⊔ Finset.sup S (fun E => C.map (pauliOp E))))
            =
          Module.finrank ℂ (↥(C.map (pauliOp E)))
            + Module.finrank ℂ (↥(Finset.sup S (fun E => C.map (pauliOp E)))) := by
        rw [← Submodule.finrank_sup_add_finrank_inf_eq]
        simp +zetaDelta at *
        exact h_orthogonal.disjoint.eq_bot

      convert h_dim_sum using 1
      · rw [Finset.sup_insert]
      ·
        rw [Finset.card_insert_of_notMem hES, ih (fun E hE => hS E (Finset.mem_insert_of_mem hE))]

        have h_inv : Function.Injective (pauliOp E) := by
          have h_inv : Invertible (pauliMatrix E) := by
            have h_inv : (pauliMatrix E).conjTranspose * pauliMatrix E = 1 := by
              ext i j
              simp +decide [Matrix.mul_apply, pauliMatrix]
              -- Since these are Pauli matrices, we know that their product is zero unless i = j.
              have h_pauli_prod :
                  ∀ k : Fin n,
                    ∑ x : Fin 2,
                      (starRingEnd ℂ ((E k).toMatrix x (i k))) * ((E k).toMatrix x (j k))
                        = if i k = j k then 1 else 0 := by
                intro k
                rcases E k with (_ | _ | _ | _) <;>
                  norm_num [Fin.sum_univ_succ, Matrix.mul_apply, PauliBasis.toMatrix]
                ·
                  rcases i_k : i k with (_ | _ | i_k) <;>
                  rcases j_k : j k with (_ | _ | j_k) <;>
                  norm_num [Fin.ext_iff, sigmaI] <;> tauto
                ·
                  rcases i_k : i k with (_ | _ | i_k) <;>
                  rcases j_k : j k with (_ | _ | j_k) <;>
                  norm_num [Fin.ext_iff, sigmaX] <;> tauto
                ·
                  rcases i_k : i k with (_ | _ | i_k) <;>
                  rcases j_k : j k with (_ | _ | j_k) <;>
                  norm_num [Fin.ext_iff, sigmaY] <;> tauto
                ·
                  rcases i_k : i k with (_ | _ | i_k) <;>
                  rcases j_k : j k with (_ | _ | j_k) <;>
                  norm_num [Fin.ext_iff, sigmaZ] <;> tauto
              simp +decide [← Finset.prod_mul_distrib, h_pauli_prod]
              rw [show
                (∑ x : Fin n → Fin 2,
                  ∏ x_1 : Fin n,
                    (starRingEnd ℂ) ((E x_1 |> PauliBasis.toMatrix) (x x_1) (i x_1)) *
                      (E x_1 |> PauliBasis.toMatrix) (x x_1) (j x_1))
                  =
                ∏ k : Fin n,
                  (∑ x : Fin 2,
                    (starRingEnd ℂ) ((E k |> PauliBasis.toMatrix) x (i k)) *
                      (E k |> PauliBasis.toMatrix) x (j k)) from by
                  exact
                    Eq.symm
                      (Fintype.prod_sum fun i_1 j_1 =>
                        (starRingEnd ℂ) ((E i_1).toMatrix j_1 (i i_1)) *
                          (E i_1).toMatrix j_1 (j i_1))]
              ·
                simp +decide [h_pauli_prod, Matrix.one_apply]
                by_cases hij : i = j <;> simp +decide [hij, Finset.prod_ite]
                exact Function.ne_iff.mp hij
            exact Matrix.invertibleOfLeftInverse _ _ h_inv
          intro x y hxy
          have h_eq : (pauliMatrix E).mulVec x = (pauliMatrix E).mulVec y := by
            exact hxy
          simpa using congr_arg (fun z => ((pauliMatrix E)⁻¹).mulVec z) h_eq

        have h_dim_map :
            ∀ (f : Hn n →ₗ[ℂ] Hn n), Function.Injective f →
              ∀ (C : Submodule ℂ (Hn n)),
                Module.finrank ℂ (↥(C.map f)) = Module.finrank ℂ C := by
          intro f hf C
          have h_iso : C ≃ₗ[ℂ] C.map f := by
            exact Submodule.equivMapOfInjective f hf C
          exact LinearEquiv.finrank_eq h_iso.symm

        have h_map_finrank :
            Module.finrank ℂ (↥(Submodule.map (pauliOp E) C)) = Module.finrank ℂ C := by
          exact h_dim_map _ h_inv _

        rw [h_map_finrank]
        ring

  exact h_dim_sum _ (fun E hE => (Finset.mem_filter.mp hE).2)

/-
Ambient dimension finrank(Hn n) = 2^n.
-/
lemma finrank_Hn (n : ℕ) : Module.finrank ℂ (Hn n) = 2^n := by
  classical
  simp [Hn, finrank_euclideanSpace, Fintype.card_fun, Fintype.card_fin]

theorem quantum_hamming_bound_raw
    (n k t : ℕ) (C : Submodule ℂ (Hn n))
    (h_dim : Module.finrank ℂ C = 2^k)
    (h_nondeg : IsNondegenerate n C t) :
    (∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j) * 2 ^ k ≤ 2 ^ n := by
  classical
  have h_sphere :
      Module.finrank ℂ (ErrorSphere n t C)
        = (∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j) * 2 ^ k := by
    simpa [h_dim, card_pauliErrorsLe, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      (error_sphere_dimension (n:=n) (t:=t) (C:=C) h_nondeg)

  have h_le :
      Module.finrank ℂ (ErrorSphere n t C) ≤ 2^n := by
    have : Module.finrank ℂ (ErrorSphere n t C) ≤ Module.finrank ℂ (Hn n) :=
      Submodule.finrank_le (ErrorSphere n t C)
    simpa [finrank_Hn n] using this

  simpa [h_sphere] using h_le


theorem quantum_hamming_bound
    (n k t : ℕ) (C : Submodule ℂ (Hn n))
    (h_dim : Module.finrank ℂ C = 2^k)
    (h_nondeg : IsNondegenerate n C t)
    (hkn : k ≤ n) :
    ∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j ≤ 2 ^ (n - k) := by
  classical
  have hraw :=
    quantum_hamming_bound_raw (n := n) (k := k) (t := t) (C := C) h_dim h_nondeg

  -- rewrite RHS: 2^n = 2^((n-k)+k) = 2^(n-k) * 2^k
  have hmul :
      (∑ j ∈ Finset.range (t + 1), n.choose j * 3 ^ j) * 2^k
        ≤ (2^(n - k)) * 2^k := by
      rwa [ ← pow_add, Nat.sub_add_cancel hkn ]
  have hkpos : 0 < 2^k := Nat.two_pow_pos k
  exact Nat.le_of_mul_le_mul_right hmul hkpos
