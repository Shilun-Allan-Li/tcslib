import TCSlib.Complexity.CircuitComplexity.Basic

/-!
# Circuit Re-indexing

Infrastructure for mapping gate indices in circuits.

## Main definitions

- `TreeCircuit.reidx`: Map gate indices through a function.
- `TreeCircuit.reidx_depth`: Re-indexing preserves depth.
- `TreeCircuit.reidx_eval`: Re-indexing commutes with evaluation.
-/

open BoolCircuit

noncomputable section

set_option maxHeartbeats 800000

namespace BoolCircuit

/-- Map gate indices of a circuit through a function `f : Fin m → Fin m'`. -/
def TreeCircuit.reidx {m m' : ℕ} : TreeCircuit m → (Fin m → Fin m') → TreeCircuit m'
  | .lit l, f => .lit ⟨f l.idx, l.sign⟩
  | .node isAnd cs, f => .node isAnd (cs.map (fun c => TreeCircuit.reidx c f))

/-- Re-indexing preserves depth. -/
theorem TreeCircuit.reidx_depth {m m' : ℕ} (c : TreeCircuit m) (f : Fin m → Fin m') :
    (TreeCircuit.reidx c f).depth = c.depth := by
  induction c using TreeCircuit.ind with
  | hlit l => simp [TreeCircuit.reidx, TreeCircuit.depth]
  | hnode isAnd cs ih =>
    simp only [TreeCircuit.reidx, TreeCircuit.depth, List.foldr_map]
    congr 1
    induction cs with
    | nil => rfl
    | cons hd tl ihtl =>
      simp only [List.foldr]
      rw [ih hd List.mem_cons_self]
      congr 1
      exact ihtl (fun c hc => ih c (List.mem_cons_of_mem _ hc))

/-- Re-indexing commutes with evaluation:
    `(c.reidx f).eval g = c.eval (g ∘ f)` -/
theorem TreeCircuit.reidx_eval {m m' : ℕ} (c : TreeCircuit m) (f : Fin m → Fin m')
    (g : Fin m' → Bool) :
    (TreeCircuit.reidx c f).eval g = c.eval (g ∘ f) := by
  induction c using TreeCircuit.ind with
  | hlit l =>
    simp [TreeCircuit.reidx, TreeCircuit.eval, Lit.eval, Function.comp]
  | hnode isAnd cs ih =>
    simp only [TreeCircuit.reidx]
    cases isAnd <;> simp only [TreeCircuit.eval, List.foldr_map] <;>
    · induction cs with
      | nil => rfl
      | cons hd tl ihtl =>
        simp only [List.foldr]
        rw [ih hd List.mem_cons_self]
        congr 1
        exact ihtl (fun c hc => ih c (List.mem_cons_of_mem _ hc))

end BoolCircuit
end
