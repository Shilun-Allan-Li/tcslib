/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import TCSlib.BooleanAnalysis.RazborovSmolensky.CircuitDegree
import Mathlib.Algebra.BigOperators.Fin

open scoped BigOperators

namespace ACP

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- The index of the `(j+1)`-st layer inside `F.nodes`, viewed as a node layer of
`F`. This is convenient for summing the non-input layers `1, …, d`. -/
def gateLayerIdx {out : Type} {n d : ℕ}
    (F : FeedForward (Fin 2) (Fin n) out) (hd : d ≤ F.depth) (j : Fin d) :
    Fin (F.depth + 1) :=
  ⟨j.1 + 1, Nat.succ_lt_succ (Nat.lt_of_lt_of_le j.2 hd)⟩

/-- `gateCountBefore` is the sum of the cardinalities of the first `d`
non-input layers. -/
lemma gateCountBefore_eq_sum_cards {out : Type} {n : ℕ}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] :
    ∀ d (hd : d ≤ F.depth),
      gateCountBefore F d hd =
        ∑ j : Fin d, Fintype.card (F.nodes (gateLayerIdx F hd j)) := by
  intro d
  induction d with
  | zero =>
      intro hd
      simp [gateCountBefore, gateLayerIdx]
  | succ d ih =>
      intro hd
      let hd' : d ≤ F.depth := Nat.le_trans (Nat.le_succ d) hd
      have hcast :
          ∀ j : Fin d, gateLayerIdx F hd (j.castSucc) = gateLayerIdx F hd' j := by
        intro j
        apply Fin.ext
        rfl
      have hlast :
          gateLayerIdx F hd (Fin.last d) = ⟨d + 1, Nat.lt_succ_of_le hd⟩ := by
        apply Fin.ext
        rfl
      have hsum :
          (∑ j : Fin d, Fintype.card (F.nodes (gateLayerIdx F hd' j))) =
            ∑ j : Fin d, Fintype.card (F.nodes (gateLayerIdx F hd (j.castSucc))) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        rw [← hcast j]
      calc
        gateCountBefore F (d + 1) hd
            = gateCountBefore F d hd' + Fintype.card (F.nodes ⟨d + 1, Nat.lt_succ_of_le hd⟩) := by
                change gateCountBefore F (d + 1) hd =
                  gateCountBefore F d (Nat.le_trans (Nat.le_succ d) hd) +
                    Fintype.card (F.nodes ⟨d + 1, Nat.lt_succ_of_le hd⟩)
                exact gateCountBefore_succ (F := F) (d := d) hd
        _ = (∑ j : Fin d, Fintype.card (F.nodes (gateLayerIdx F hd' j))) +
              Fintype.card (F.nodes ⟨d + 1, Nat.lt_succ_of_le hd⟩) := by
                rw [ih hd']
        _ = (∑ j : Fin d, Fintype.card (F.nodes (gateLayerIdx F hd (j.castSucc)))) +
              Fintype.card (F.nodes (gateLayerIdx F hd (Fin.last d))) := by
                rw [hsum, hlast]
        _ = ∑ j : Fin (d + 1), Fintype.card (F.nodes (gateLayerIdx F hd j)) := by
              let f : Fin (d + 1) → ℕ := fun j =>
                Fintype.card (F.nodes (gateLayerIdx F hd j))
              change (∑ j : Fin d, f j.castSucc) + f (Fin.last d) = ∑ j : Fin (d + 1), f j
              exact (Fin.sum_univ_castSucc (f := f)).symm

/-- The circuit size is the sum of the cardinalities of all non-input layers. -/
lemma size_eq_sum_cards {out : Type} {n : ℕ}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] :
    F.size = ∑ d : Fin F.depth, Fintype.card (F.nodes d.succ) := by
  rw [FeedForward.size, Nat.card_sigma]
  refine Finset.sum_congr rfl ?_
  intro d _
  simp

/-- At full depth, `gateCountBefore` is exactly the total circuit size. -/
lemma gateCountBefore_depth_eq_size {out : Type} {n : ℕ}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Fintype (F.nodes i)] :
    gateCountBefore F F.depth (Nat.le_refl F.depth) = F.size := by
  calc
    gateCountBefore F F.depth (Nat.le_refl F.depth)
        = ∑ j : Fin F.depth, Fintype.card (F.nodes (gateLayerIdx F (Nat.le_refl F.depth) j)) := by
            exact gateCountBefore_eq_sum_cards (F := F) F.depth (Nat.le_refl F.depth)
    _ = ∑ j : Fin F.depth, Fintype.card (F.nodes j.succ) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          have hidx : gateLayerIdx F (Nat.le_refl F.depth) j = j.succ := by
            apply Fin.ext
            rfl
          rw [hidx]
    _ = F.size := by
          symm
          exact size_eq_sum_cards (F := F)

/-- Simultaneous pointwise polynomial distribution for all output nodes, with the
error bound stated using the total number of gates. -/
theorem exists_poly_distribution_for_circuit_outputs_size {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Finite (F.nodes i)]
    [Fintype out]
    (hUses : F.onlyUsesGates (ACp_GateOps p)) (ℓ : ℕ) :
    ∃ (Seed : Type) (_ : Fintype Seed) (_ : DecidableEq Seed)
      (P : Seed → out → MvPolynomial (Fin n) (ZMod p)),
      0 < Fintype.card Seed ∧
      (∀ s o, (P s o).totalDegree ≤ circuitDegreeBound p ℓ F.depth) ∧
      ∀ x : Fin n → Fin 2,
        (Finset.univ.filter (fun s : Seed =>
          ∃ o : out,
            (P s o).eval (boolInput (p := p) x) ≠
              (((F.eval x o : Fin 2) : Nat) : ZMod p))).card * 2 ^ ℓ ≤
          F.size * Fintype.card Seed := by
  classical
  letI : ∀ i, Fintype (F.nodes i) := fun i => Fintype.ofFinite (F.nodes i)
  rcases exists_poly_distribution_for_circuit_outputs (p := p) F hUses ℓ with
    ⟨Seed, instF, instD, P, hpos, hdeg, hbad⟩
  refine ⟨Seed, instF, instD, P, hpos, hdeg, ?_⟩
  intro x
  simpa [gateCountBefore_depth_eq_size (F := F)] using hbad x

/-- Pointwise distribution for a single-output circuit, with the error bound
stated using the total number of gates. -/
theorem exists_poly_distribution_for_circuit_one_size {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACp_GateOps p)) (ℓ : ℕ) :
    ∃ (Seed : Type) (_ : Fintype Seed) (_ : DecidableEq Seed)
      (P : Seed → MvPolynomial (Fin n) (ZMod p)),
      0 < Fintype.card Seed ∧
      (∀ s, (P s).totalDegree ≤ circuitDegreeBound p ℓ F.depth) ∧
      ∀ x : Fin n → Fin 2,
        (Finset.univ.filter (fun s : Seed =>
          (P s).eval (boolInput (p := p) x) ≠
            (((F.eval₁ x : Fin 2) : Nat) : ZMod p))).card * 2 ^ ℓ ≤
          F.size * Fintype.card Seed := by
  classical
  letI : ∀ i, Fintype (F.nodes i) := fun i => Fintype.ofFinite (F.nodes i)
  rcases exists_poly_distribution_for_circuit_one (p := p) F hUses ℓ with
    ⟨Seed, instF, instD, P, hpos, hdeg, hbad⟩
  refine ⟨Seed, instF, instD, P, hpos, hdeg, ?_⟩
  intro x
  simpa [gateCountBefore_depth_eq_size (F := F)] using hbad x

/-- The list formulation of the single-output circuit theorem, with the error
bound stated using the total number of gates. -/
theorem exists_poly_list_for_circuit_one_size {n : ℕ} {out : Type}
    (F : FeedForward (Fin 2) (Fin n) out)
    [∀ i, Finite (F.nodes i)]
    [Unique out]
    (hUses : F.onlyUsesGates (ACp_GateOps p)) (ℓ : ℕ) :
    ∃ Ps : List (MvPolynomial (Fin n) (ZMod p)),
      0 < Ps.length ∧
      (∀ P ∈ Ps, P.totalDegree ≤ circuitDegreeBound p ℓ F.depth) ∧
      ∀ x : Fin n → Fin 2,
        (Ps.filter (fun P =>
          P.eval (boolInput (p := p) x) ≠
            (((F.eval₁ x : Fin 2) : Nat) : ZMod p))).length * 2 ^ ℓ ≤
          F.size * Ps.length := by
  classical
  letI : ∀ i, Fintype (F.nodes i) := fun i => Fintype.ofFinite (F.nodes i)
  rcases exists_poly_list_for_circuit_one (p := p) F hUses ℓ with
    ⟨Ps, hpos, hdeg, hbad⟩
  refine ⟨Ps, hpos, hdeg, ?_⟩
  intro x
  simpa [gateCountBefore_depth_eq_size (F := F)] using hbad x

end ACP
