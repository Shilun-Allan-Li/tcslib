import TCSlib.Complexity.CircuitComplexity.NANDLayering

/-! Probe P9 (6a statement job): the layering conversion on three NAND-form circuits.
* `xorC`: XOR of two inputs from four NAND gates (a gap of 2 from `x₀` to gate 3);
* `oddC`: `NAND(x₀, NAND(NAND(x₁)))`, whose last gate reads `x₀` across an **odd** gap of 3;
* `zeroC`: a fan-in-0 gate `NAND[]` (level 1) read at level 3, so its parity twin
  `NAND(NAND(x₀, ¬x₀))` is used.
For each, the layered circuit is rebuilt from `layerGates`/`layerOutput` with acyclicity and the
output bound proved by kernel `decide` (so N12–N13 hold on these instances and the probe does not
depend on the admitted fields), and the probe checks by kernel `decide`:
`eval (litInput x) = C.eval x` on every input (N7), `IsLayered` (N8), `IsNANDForm` (N9),
depth equal to `C.depth` (N10) and the size bound of N11.  The same checks on `C.layerNAND` itself
are also run (they depend on the admitted N12–N13 only through proof fields).  The final block
records the odd-gap finding: a layered NAND circuit over **positive** inputs computes a monotone
function at even depth and an antimonotone one at odd depth, and XOR (depth 3 here) is neither
(checked on its truth table), so the literal inputs are necessary. -/

namespace P9
open BoolCircuit

def inp (a b : Bool) : Fin 2 → Bool := fun i => if i.val = 0 then a else b

/-- XOR in NAND form: `v2 = NAND(x0,x1)`, `v3 = NAND(x0,v2)`, `v4 = NAND(x1,v2)`, `v5 = NAND(v3,v4)`. -/
def xorC : DAGCircuit 2 where
  gates := [⟨.not, [0, 1]⟩, ⟨.not, [0, 2]⟩, ⟨.not, [1, 2]⟩, ⟨.not, [3, 4]⟩]
  output := 5
  args_lt := by decide
  output_lt := by decide

/-- Odd gap: `v2 = NAND(x1)`, `v3 = NAND(v2)`, `v4 = NAND(x0, v3)` (`x₀` read across 3 levels). -/
def oddC : DAGCircuit 2 where
  gates := [⟨.not, [1]⟩, ⟨.not, [2]⟩, ⟨.not, [0, 3]⟩]
  output := 4
  args_lt := by decide
  output_lt := by decide

/-- Fan-in 0: `v2 = NAND[]` (false), `v3 = NAND[x0]`, `v4 = NAND[v3]`, `v5 = NAND[v2, v4]`. -/
def zeroC : DAGCircuit 2 where
  gates := [⟨.not, []⟩, ⟨.not, [0]⟩, ⟨.not, [3]⟩, ⟨.not, [2, 4]⟩]
  output := 5
  args_lt := by decide
  output_lt := by decide

/-- The layered circuit rebuilt with its fields proved by `decide` on the instance. -/
def xorL : DAGCircuit 4 :=
  ⟨xorC.layerGates, xorC.layerOutput, by decide, by decide⟩
def oddL : DAGCircuit 4 :=
  ⟨oddC.layerGates, oddC.layerOutput, by decide, by decide⟩
def zeroL : DAGCircuit 4 :=
  ⟨zeroC.layerGates, zeroC.layerOutput, by decide, by decide⟩

/-- All checks on a layered instance `L` of `C`. -/
def ok (C : DAGCircuit 2) (L : DAGCircuit 4) : Bool :=
  [false, true].all (fun a => [false, true].all (fun b =>
    L.eval (litInput (inp a b)) == C.eval (inp a b))) &&
  decide L.IsLayered && decide L.IsNANDForm && decide C.IsNANDForm &&
  (L.depth == C.depth) && decide (L.size ≤ 2 * 2 + (2 * C.depth + 1) * C.size)

theorem xor_ok : ok xorC xorL = true := by decide
theorem odd_ok : ok oddC oddL = true := by decide
theorem zero_ok : ok zeroC zeroL = true := by decide

/-- The same checks on `C.layerNAND` (its gates and output are the same terms). -/
theorem xor_ok' : ok xorC xorC.layerNAND = true := by decide
theorem odd_ok' : ok oddC oddC.layerNAND = true := by decide
theorem zero_ok' : ok zeroC zeroC.layerNAND = true := by decide

/-- The source circuits are not layered (so the conversion is doing work), and the odd-gap and
fan-in-0 circuits exercise the parity twin. -/
theorem sources_not_layered : (decide xorC.IsLayered, decide oddC.IsLayered,
    decide zeroC.IsLayered) = (false, false, false) := by decide

/-- Depths of the sources and their layerings: `(3, 3, 3)` both. -/
theorem depths : ((xorC.depth, oddC.depth, zeroC.depth), (xorL.depth, oddL.depth, zeroL.depth)) =
    ((3, 3, 3), (3, 3, 3)) := by decide

/-- The odd-gap finding (r3 §H3.13): the truth table of XOR (`xorC`). -/
def xorTable : List Bool := [xorC.eval (inp false false), xorC.eval (inp true false),
  xorC.eval (inp false true), xorC.eval (inp true true)]

theorem xor_table : xorTable = [false, true, true, false] := by decide

/-- XOR is not antimonotone: `f(0,0) = 0 < 1 = f(1,0)`, and not monotone: `f(1,0) = 1 > 0 =
f(1,1)`; so no layered NAND circuit of depth 3 over the positive inputs computes it, and the
literal inputs are necessary (r3 §H3.13). -/
theorem xor_neither : xorTable.getD 0 true = false ∧ xorTable.getD 1 false = true ∧
    xorTable.getD 3 true = false := by decide

end P9

#eval (P9.xorC.layerGates, P9.xorC.layerOutput)
#eval (P9.oddC.layerGates, P9.oddC.layerOutput)
#eval (P9.zeroC.layerGates, P9.zeroC.layerOutput)
#eval (P9.xorL.size, P9.oddL.size, P9.zeroL.size)
