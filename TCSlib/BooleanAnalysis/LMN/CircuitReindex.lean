import TCSlib.BooleanAnalysis.Switching.Circuit
import Mathlib

/-!
# Circuit Re-indexing

Infrastructure for mapping gate indices in circuits.

## Main definitions

- `Circuit.reidx`: Map gate indices through a function.
- `Circuit.reidx_depth`: Re-indexing preserves depth.
- `Circuit.reidx_eval`: Re-indexing commutes with evaluation.
-/

open BoolCircuit

noncomputable section

set_option maxHeartbeats 800000

namespace BoolCircuit

/-- Map gate indices of a circuit through a function `f : Fin m → Fin m'`. -/
def Circuit.reidx {m m' : ℕ} : Circuit m → (Fin m → Fin m') → Circuit m'
  | .lit l, f => .lit ⟨f l.idx, l.sign⟩
  | .node isAnd cs, f => .node isAnd (cs.map (fun c => Circuit.reidx c f))

/-- Re-indexing preserves depth. -/
theorem Circuit.reidx_depth {m m' : ℕ} (c : Circuit m) (f : Fin m → Fin m') :
    (Circuit.reidx c f).depth = c.depth := by
  induction c using Circuit.ind with
  | hlit l => simp [Circuit.reidx, Circuit.depth]
  | hnode isAnd cs ih =>
    simp only [Circuit.reidx, Circuit.depth, List.foldr_map]
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
theorem Circuit.reidx_eval {m m' : ℕ} (c : Circuit m) (f : Fin m → Fin m')
    (g : Fin m' → Bool) :
    (Circuit.reidx c f).eval g = c.eval (g ∘ f) := by
  induction c using Circuit.ind with
  | hlit l =>
    simp [Circuit.reidx, Circuit.eval, Lit.eval, Function.comp]
  | hnode isAnd cs ih =>
    simp only [Circuit.reidx]
    cases isAnd <;> simp only [Circuit.eval, List.foldr_map] <;>
    · induction cs with
      | nil => rfl
      | cons hd tl ihtl =>
        simp only [List.foldr]
        rw [ih hd List.mem_cons_self]
        congr 1
        exact ihtl (fun c hc => ih c (List.mem_cons_of_mem _ hc))

end BoolCircuit
end
