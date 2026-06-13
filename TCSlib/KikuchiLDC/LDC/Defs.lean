/-
  LDC/Defs.lean
  Core definitions following Sections 2–4 of the blueprint:
    • Hypergraphs (Definition 3.1–3.3)
    • Locally Decodable Codes (Definition 3.4–3.5)
    • XOR instances and their value (Definition 3.6–3.7)
    • Double-copy notation (Notation 2.2)
-/
import Mathlib

open Finset BigOperators

noncomputable section

/-! ## §3.1 Hypergraphs -/

/-- Definition 3.1: A hypergraph on vertex set `Fin n` is a finite multiset of
    subsets of `Fin n`. We model it as a `Finset (Finset (Fin n))`. -/
abbrev Hypergraph (n : ℕ) := Finset (Finset (Fin n))

/-- Definition 3.2: A hypergraph is `q`-uniform if every edge has exactly `q` vertices. -/
def Hypergraph.IsUniform (H : Hypergraph n) (q : ℕ) : Prop :=
  ∀ C ∈ H, C.card = q

/-- Definition 3.2: A hypergraph is a matching if all edges are pairwise disjoint. -/
def Hypergraph.IsMatching (H : Hypergraph n) : Prop :=
  ∀ C ∈ H, ∀ C' ∈ H, C ≠ C' → Disjoint C C'

/-- Definition 3.3: The degree of a set `Q` in hypergraph `H` is the number of
    edges containing `Q`. -/
def Hypergraph.degree (H : Hypergraph n) (Q : Finset (Fin n)) : ℕ :=
  (H.filter (fun C => Q ⊆ C)).card

/-- The pair-degree bound: all pairs have degree ≤ d. -/
def Hypergraph.pairDegreeBound (H : Hypergraph n) (d : ℕ) : Prop :=
  ∀ u v : Fin n, u ≠ v → H.degree {u, v} ≤ d

/-! ## §3.2 Locally Decodable Codes (Normal Form) -/

/-- A sign assignment: elements of `{-1, 1}` represented as `ℤ`. -/
def IsPMOne (x : ℤ) : Prop := x = 1 ∨ x = -1

/-- Definition 3.5 (Normal Form LDC):
    A `(3, δ, ε)`-normally decodable code `C : (Fin k → ℤ) → (Fin n → ℤ)` consists of:
    - For each `i : Fin k`, a 3-uniform matching `H_i` on `Fin n`
    - `|H_i| ≥ δ * n`
    - For every `C ∈ H_i` and every message `b`:
        `Pr_b[b_i = ∏_{v ∈ C} C(b)_v] ≥ 1/2 + ε`
    We package just the structural data and the key consequences. -/
structure NormalLDC (k n : ℕ) where
  /-- The matchings for each message bit. -/
  matching : Fin k → Hypergraph n
  /-- Each matching is 3-uniform. -/
  uniform : ∀ i, (matching i).IsUniform 3
  /-- Each matching is indeed a matching (pairwise disjoint edges). -/
  isMatching : ∀ i, (matching i).IsMatching
  /-- Density parameter δ > 0. -/
  delta : ℝ
  delta_pos : 0 < delta
  /-- Advantage parameter ε > 0. -/
  epsilon : ℝ
  epsilon_pos : 0 < epsilon
  /-- Each matching has at least δ·n edges. -/
  matching_size : ∀ i, delta * n ≤ (matching i).card

/-! ## §3.3 XOR Instances and Value -/

/-- The combined hypergraph: union of all matchings. -/
def NormalLDC.combined {k n : ℕ} (L : NormalLDC k n) : Hypergraph n :=
  Finset.biUnion Finset.univ L.matching

/-- Total number of constraints: m = ∑_i |H_i|. -/
def NormalLDC.totalConstraints {k n : ℕ} (L : NormalLDC k n) : ℕ :=
  ∑ i : Fin k, (L.matching i).card

/-- For `x : Fin n → ℤ` (assignment in ±1) and `C : Finset (Fin n)`,
    define `x_C = ∏_{v ∈ C} x_v`. -/
def assignment_prod (x : Fin n → ℤ) (C : Finset (Fin n)) : ℤ :=
  ∏ v ∈ C, x v

/-- Definition 3.7: The XOR polynomial
    `ψ_b(x) = (1/m) ∑_i b_i ∑_{C ∈ H_i} ∏_{v ∈ C} x_v`. -/
def NormalLDC.xorPoly {k n : ℕ} (L : NormalLDC k n)
    (b : Fin k → ℤ) (x : Fin n → ℤ) : ℝ :=
  (1 / (L.totalConstraints : ℝ)) *
    ∑ i : Fin k, (b i : ℝ) *
      ∑ C ∈ L.matching i, (assignment_prod x C : ℝ)

/-- `val(ψ_b)`: the maximum value of the XOR polynomial over ±1 assignments. -/
def NormalLDC.xorVal {k n : ℕ} (L : NormalLDC k n) (b : Fin k → ℤ) : ℝ :=
  ⨆ (x : Fin n → ℤ) (_ : ∀ v, IsPMOne (x v)), L.xorPoly b x

/-! ## §2.2 Double-Copy Notation -/

/-- The double-copy ground set `Fin n × Fin 2`. -/
abbrev DoubleCopy (n : ℕ) := Fin n × Fin 2

/-- For `u : Fin n`, the first copy `u^(1) = (u, 0)`. -/
def copy1 (u : Fin n) : DoubleCopy n := (u, 0)

/-- For `u : Fin n`, the second copy `u^(2) = (u, 1)`. -/
def copy2 (u : Fin n) : DoubleCopy n := (u, 1)

/-- For `C ⊆ Fin n`, the first-copy embedding `C^(1)`. -/
def liftCopy1 (C : Finset (Fin n)) : Finset (DoubleCopy n) :=
  C.map ⟨copy1, fun _ _ h => by simp [copy1] at h; exact h⟩

/-- For `C ⊆ Fin n`, the second-copy embedding `C^(2)`. -/
def liftCopy2 (C : Finset (Fin n)) : Finset (DoubleCopy n) :=
  C.map ⟨copy2, fun _ _ h => by simp [copy2] at h; exact h⟩

end

