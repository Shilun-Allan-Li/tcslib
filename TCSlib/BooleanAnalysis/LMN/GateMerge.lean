import TCSlib.BooleanAnalysis.LMN.CircuitReindex

/-!
# Gate Set Merging

Infrastructure for merging two gate arrays indexed by `Fin m₁` and `Fin m₂`
into one indexed by `Fin (m₁ + m₂)`, together with lemmas showing
that `Circuit.reidx` correctly reroutes evaluation through the merged array.
-/

open BoolCircuit

noncomputable section

set_option maxHeartbeats 400000

namespace LMN

variable {n : ℕ}

/-- Merge two gate arrays. Indices `0 .. m₁-1` come from `g₁`,
    indices `m₁ .. m₁+m₂-1` come from `g₂`. -/
def mergeGates {α : Type*} {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → α) (g₂ : Fin m₂ → α) : Fin (m₁ + m₂) → α :=
  fun j => if h : j.val < m₁ then g₁ ⟨j.val, h⟩ else g₂ ⟨j.val - m₁, by omega⟩

@[simp]
lemma mergeGates_castAdd {α : Type*} {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → α) (g₂ : Fin m₂ → α) (i : Fin m₁) :
    mergeGates g₁ g₂ (Fin.castAdd m₂ i) = g₁ i := by
  unfold mergeGates
  simp [i.isLt]

@[simp]
lemma mergeGates_natAdd {α : Type*} {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → α) (g₂ : Fin m₂ → α) (i : Fin m₂) :
    mergeGates g₁ g₂ (Fin.natAdd m₁ i) = g₂ i := by
  unfold mergeGates
  have : ¬ (m₁ + i.val < m₁) := by omega
  simp [this]

/-- Reidx into the left half + mergeGates = original evaluation. -/
lemma reidx_eval_mergeGates_left {m₁ m₂ : ℕ} (c : Circuit m₁)
    (g₁ : Fin m₁ → Bool) (g₂ : Fin m₂ → Bool) :
    (Circuit.reidx c (Fin.castAdd m₂)).eval (mergeGates g₁ g₂) = c.eval g₁ := by
  rw [Circuit.reidx_eval]; congr 1; ext i; simp

/-- Reidx into the right half + mergeGates = original evaluation. -/
lemma reidx_eval_mergeGates_right {m₁ m₂ : ℕ} (c : Circuit m₂)
    (g₁ : Fin m₁ → Bool) (g₂ : Fin m₂ → Bool) :
    (Circuit.reidx c (Fin.natAdd m₁)).eval (mergeGates g₁ g₂) = c.eval g₂ := by
  rw [Circuit.reidx_eval]; congr 1; ext i; simp

/-- Width preservation for merged gates (left part). -/
lemma mergeGates_width_left {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → DNF n) (g₂ : Fin m₂ → DNF n) (l : ℕ)
    (h₁ : ∀ k, (g₁ k).width ≤ l) (i : Fin m₁) :
    (mergeGates g₁ g₂ (Fin.castAdd m₂ i)).width ≤ l := by
  simp [h₁]

/-- Width preservation for merged gates (right part). -/
lemma mergeGates_width_right {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → DNF n) (g₂ : Fin m₂ → DNF n) (l : ℕ)
    (h₂ : ∀ k, (g₂ k).width ≤ l) (i : Fin m₂) :
    (mergeGates g₁ g₂ (Fin.natAdd m₁ i)).width ≤ l := by
  simp [h₂]

/-- Width preservation for all merged gates. -/
lemma mergeGates_width {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → DNF n) (g₂ : Fin m₂ → DNF n) (l : ℕ)
    (h₁ : ∀ k, (g₁ k).width ≤ l) (h₂ : ∀ k, (g₂ k).width ≤ l)
    (k : Fin (m₁ + m₂)) :
    (mergeGates g₁ g₂ k).width ≤ l := by
  unfold mergeGates; split <;> [exact h₁ _; exact h₂ _]

/-- Var injectivity for all merged gates. -/
lemma mergeGates_varInj {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → DNF n) (g₂ : Fin m₂ → DNF n)
    (h₁ : ∀ k, ∀ t ∈ g₁ k, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (h₂ : ∀ k, ∀ t ∈ g₂ k, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂)
    (k : Fin (m₁ + m₂)) :
    ∀ t ∈ mergeGates g₁ g₂ k, ∀ l₁ ∈ t, ∀ l₂ ∈ t, l₁.var = l₂.var → l₁ = l₂ := by
  unfold mergeGates; split <;> [exact h₁ _; exact h₂ _]

/-- Nodup for all merged gates. -/
lemma mergeGates_nodup {m₁ m₂ : ℕ}
    (g₁ : Fin m₁ → DNF n) (g₂ : Fin m₂ → DNF n)
    (h₁ : ∀ k, ∀ t ∈ g₁ k, t.Nodup)
    (h₂ : ∀ k, ∀ t ∈ g₂ k, t.Nodup)
    (k : Fin (m₁ + m₂)) :
    ∀ t ∈ mergeGates g₁ g₂ k, t.Nodup := by
  unfold mergeGates; split <;> [exact h₁ _; exact h₂ _]

end LMN
end
