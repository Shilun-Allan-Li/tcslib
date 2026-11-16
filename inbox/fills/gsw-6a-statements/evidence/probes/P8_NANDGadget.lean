import TCSlib.Complexity.CircuitComplexity.NANDForm

/-! Probe P8 (6a statement job): every row of r3 §H3.9's NAND-gadget table.
For each old gate `g` (∧, ∨, ¬ with 0, 1, 2 and repeated arguments) and two prefixes `gs`
(empty, and one existing gate), `nandGadget 2 g gs` is checked to
* extend `gs`, stay acyclic and return a vertex below the new length,
* compute `g` on every input (vertexValue against `g.eval` of the old run),
* add at most 2 levels over the deepest argument and at most `fan-in + 2` gates,
* emit only NAND gates.
Kernel `decide` only (no `native_decide`). Probes may unfold library definitions. -/

namespace P8
open BoolCircuit

/-- The input `(a, b)` on two variables. -/
def inp (a b : Bool) : Fin 2 → Bool := fun i => if i.val = 0 then a else b

def rowOK (g : DAGGate) (gs : List DAGGate) : Bool :=
  let r := nandGadget 2 g gs
  let ext := r.1.drop gs.length
  (r.1.take gs.length == gs) &&
  decide (r.2 < 2 + r.1.length) &&
  (List.range r.1.length).all (fun i => (r.1.getD i ⟨.and, []⟩).args.all (· < 2 + i)) &&
  [false, true].all (fun a => [false, true].all (fun b =>
    vertexValue r.1 (inp a b) r.2 == g.eval (runWith DAGGate.eval gs (List.ofFn (inp a b))))) &&
  decide (vertexDepth 2 r.1 r.2 ≤ 2 + (g.args.map (vertexDepth 2 gs)).foldr max 0) &&
  decide (r.1.length ≤ gs.length + (g.args.length + 2)) &&
  ext.all (fun h => decide h.IsNAND)

/-- The table rows of r3 §H3.9 over inputs `0, 1` and, with the prefix, the gate vertex `2`. -/
def rows : List DAGGate :=
  [⟨.and, []⟩, ⟨.or, []⟩, ⟨.not, []⟩,
   ⟨.and, [0]⟩, ⟨.or, [0]⟩, ⟨.not, [0]⟩,
   ⟨.and, [0, 1]⟩, ⟨.or, [0, 1]⟩, ⟨.not, [0, 1]⟩,
   ⟨.and, [1, 1]⟩, ⟨.or, [1, 1]⟩, ⟨.not, [1, 1]⟩]

def rowsWithGate : List DAGGate :=
  rows ++ [⟨.and, [2, 0]⟩, ⟨.or, [2, 1]⟩, ⟨.not, [2, 2]⟩, ⟨.and, [2]⟩, ⟨.or, [2, 2]⟩]

theorem rows_empty_prefix : rows.all (fun g => rowOK g []) = true := by decide

theorem rows_one_gate_prefix :
    rowsWithGate.all (fun g => rowOK g [⟨.or, [0, 1]⟩]) = true := by decide

/-- Gate counts per row (r3 §H3.9 column "gates"): 2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1. -/
theorem gate_counts : rows.map (fun g => (nandGadget 2 g []).1.length) =
    [2, 1, 1, 2, 2, 1, 2, 3, 1, 2, 3, 1] := by decide

/-- Depth added per row from inputs (column "depth added"): 2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1. -/
theorem depths : rows.map (fun g => vertexDepth 2 (nandGadget 2 g []).1 (nandGadget 2 g []).2) =
    [2, 1, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1] := by decide

end P8

#eval P8.rows.map (fun g => (BoolCircuit.nandGadget 2 g []))
