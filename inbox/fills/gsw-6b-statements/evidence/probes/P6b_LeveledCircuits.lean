import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! Probe P6b (gsw-6b statements, check 7): `leveledEval` and `leveledEvalCircuit` on 6a's circuits.
Parameters `A0 = (n = 0, m = 2, q = 2, ℓ = 1)` (`N = 1`; one bootstrapped gate ≈ 1 minute of
`#eval`): at `n = 0` every secret is the empty vector, so this probe checks the plumbing (levels
`depthAt`, the level-key choice `δ − 1`, literal ciphertexts, the layering and the padding), not key
separation (P6a does that at `n = 1`). Noise-free keys: `L + 1` honest keys (all `(0, 0)` at `n = 0`).
* (run) the layering of `twoC = NAND(x₀, NAND(x₁))`, the smallest NAND-form circuit whose layering needs a parity
  twin, on all four inputs (the lead's reduced order); the larger circuits below are defined and checked for
  layering by `decide`, but not run (each ≈ 17–19 bootstrapped gates);
* the layered circuits `xorC.layerNAND` and `oddC.layerNAND` of 6a's probe P9 (rebuilt from their data with
  fields proved by `decide`, `rfl`-equal to `layerNAND`'s) (XOR, and the odd-gap
  circuit `NAND(x₀, NAND(NAND(x₁)))`; layered and NAND form by `decide`) run by `leveledEval` (strict
  `leveledEvalA`, proved equal) with `L = 3` on `literalCts` of noise-free encryptions of one input
  each: the output equals `(Cc.eval x) • G` and decrypts to `Cc.eval x` (= the source circuit's value);
* `leveledEvalCircuit` on the one-gate circuit `AND(x₀, x₁)` (fan-in 2, not NAND form; through
  `toNANDForm` and `layerNAND`): the strict version `leveledEvalCircuitA` is proved equal, but not run (the
  lead's reduced order: one circuit only). Running it needs `#eval!`, since `toNANDForm`'s proof field
  is the admitted N2 (6a) while its data is sorry-free.
* Cap: the run is capped at 25 minutes (`tools/probe/run_capped.sh`); the inputs evaluated before the cap
  are in `P6b_LeveledCircuits.progress`.
-/

open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit BranchingProgram

namespace P6
/-! #### Tabulated program maps (probe-local; proved equal) -/
/-- A map `Fin w → Fin w` read from a precomputed array (the array is an argument, evaluated
before the call). -/
@[noinline] def tabOf {w : ℕ} (a : Array (Fin w)) (h : a.size = w) : Fin w → Fin w :=
  fun i => a[i.val]'(by rw [h]; exact i.isLt)

/-- `f` tabulated once. -/
def tabF {w : ℕ} (f : Fin w → Fin w) : Fin w → Fin w :=
  tabOf (Array.ofFn f) (Array.size_ofFn)

theorem tabF_eq {w : ℕ} (f : Fin w → Fin w) : tabF f = f := by
  funext i; simp only [tabF, tabOf, Array.getElem_ofFn]

/-- A branching program with every map tabulated. -/
def tabB {w k : ℕ} (B : BranchingProgram w k) : BranchingProgram w k :=
  ⟨B.instrs.map fun ι => ⟨ι.var, tabF ι.map0, tabF ι.map1⟩⟩

theorem tabB_eq {w k : ℕ} (B : BranchingProgram w k) : tabB B = B := by
  obtain ⟨l⟩ := B
  have h : (fun ι : BranchingProgram.Instr w k => (⟨ι.var, tabF ι.map0, tabF ι.map1⟩ :
      BranchingProgram.Instr w k)) = id := by
    funext ι; simp only [tabF_eq, id]
  simp only [tabB, h, List.map_id]

/-! #### Strict array evaluator (probe-local; proved equal to the library definitions)
`#eval` of the library's `homEvalPBP` folds closures: every access to a state entry recomputes
the earlier steps, so the run is exponential in the program length (a first evaluator that
re-materialized a closure state was not strict either). `evalA` folds over **arrays** (a strict
accumulator), converting to and from the function state at each step; `evalA_eq` proves
`ofArr P (evalA P B cts V) = homEvalPBP P B cts V` through the readers `homEvalPBP_eq` and
`BranchingProgram.evalWith_eq`, so `#eval` of `evalA` evaluates `homEvalPBP` itself. -/

/-- A state as nested arrays. -/
def toArr (P : Parameters) {w : ℕ} (V : Fin w → Ciphertext P) :
    Array (Array (Array (ZMod P.lwe.modulus))) :=
  Array.ofFn fun k => Array.ofFn fun i => Array.ofFn fun j => V k i j

/-- The function state of nested arrays (default `0` out of range). Not inlined, so the array is
evaluated before the closure is built. -/
@[noinline] def ofArr (P : Parameters) {w : ℕ} (A : Array (Array (Array (ZMod P.lwe.modulus)))) :
    Fin w → Ciphertext P :=
  fun k i j => ((A.getD k.val #[]).getD i.val #[]).getD j.val 0

theorem ofArr_toArr (P : Parameters) {w : ℕ} (V : Fin w → Ciphertext P) :
    ofArr P (toArr P V) = V := by
  funext k i j
  simp [ofArr, toArr, Array.getD_eq_getD_getElem?]

/-- `homEvalPBP`'s fold over a strict array accumulator. -/
@[noinline] def evalA (P : Parameters) {w k : ℕ} (B : BranchingProgram w k) (cts : Fin k → Ciphertext P)
    (V : Fin w → Ciphertext P) : Array (Array (Array (ZMod P.lwe.modulus))) :=
  B.instrs.foldl (fun S ι => toArr P (ι.stepWith (select P) cts (ofArr P S))) (toArr P V)

theorem evalA_eq (P : Parameters) {w k : ℕ} (B : BranchingProgram w k)
    (cts : Fin k → Ciphertext P) (V : Fin w → Ciphertext P) :
    ofArr P (evalA P B cts V) = homEvalPBP P B cts V := by
  rw [homEvalPBP_eq, BranchingProgram.evalWith_eq, evalA]
  have key : ∀ (l : List (BranchingProgram.Instr w k)) (S : Array (Array (Array (ZMod P.lwe.modulus)))),
      ofArr P (l.foldl (fun S ι => toArr P (ι.stepWith (select P) cts (ofArr P S))) S) =
        l.foldl (fun U ι => ι.stepWith (select P) cts U) (ofArr P S) := by
    intro l
    induction l with
    | nil => intro S; rfl
    | cons ι l ih => intro S; rw [List.foldl_cons, ih, ofArr_toArr, List.foldl_cons]
  rw [key, ofArr_toArr]

/-- A ciphertext as a strict array matrix and back (for inputs). -/
def matA (P : Parameters) (M : Ciphertext P) : Ciphertext P :=
  ofArr P (w := 1) (toArr P (w := 1) fun _ => M) 0

theorem matA_eq (P : Parameters) (M : Ciphertext P) : matA P M = M := by
  rw [matA, ofArr_toArr]

/-- `homEvalFormula` through `evalA`, on the tabulated program. -/
def formulaA (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) : Ciphertext P :=
  ofArr P (w := 5) (evalA P (tabB (barrington c sigma1)) (fun j => matA P (cts j))
    (Pi.single 0 (gadget P))) (sigma1 0)

theorem formulaA_eq (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) : formulaA P c cts = homEvalFormula P c cts := by
  have h : (fun j => matA P (cts j)) = cts := funext fun j => matA_eq P (cts j)
  rw [formulaA, h, evalA_eq, tabB_eq, homEvalFormula_eq]

/-- `bootNAND` through `formulaA`. -/
def bootNANDA (P : Parameters) (evk : Fin P.columns → Ciphertext P) (C₁ C₂ : Ciphertext P) :
    Ciphertext P :=
  formulaA P (nandFormula P C₁ C₂) evk

theorem bootNANDA_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P) (C₁ C₂ : Ciphertext P) :
    bootNANDA P evk C₁ C₂ = bootNAND P evk C₁ C₂ := by
  rw [bootNANDA, formulaA_eq, bootNAND_eq]

/-- `bootGate` with `bootNANDA`. -/
def bootGateA (P : Parameters) (evk : Fin P.columns → Ciphertext P) (g : DAGGate)
    (cts : List (Ciphertext P)) : Ciphertext P :=
  match g.args with
  | [] => bootNANDA P evk (gadget P) (gadget P)
  | [a] => bootNANDA P evk (cts.getD a 0) (cts.getD a 0)
  | a :: b :: _ => bootNANDA P evk (cts.getD a 0) (cts.getD b 0)

theorem bootGateA_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P) :
    bootGateA P evk = bootGate P evk := by
  funext g cts
  rcases hg : g.args with _ | ⟨a, _ | ⟨b, l⟩⟩
  · rw [bootGate_of_args_eq_nil P evk g cts hg, ← bootNANDA_eq]; simp only [bootGateA, hg]
  · rw [bootGate_of_args_eq_singleton P evk g cts a hg, ← bootNANDA_eq]; simp only [bootGateA, hg]
  · rw [bootGate_of_args_eq_cons_cons P evk g cts a b l hg, ← bootNANDA_eq]
    simp only [bootGateA, hg]

/-- `fheEval` with `bootGateA`. -/
def fheEvalA (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ} (Cc : DAGCircuit k)
    (cts : Fin k → Ciphertext P) : Ciphertext P :=
  (runWith (bootGateA P evk) Cc.gates (List.ofFn cts)).getD Cc.output 0

theorem fheEvalA_eq (P : Parameters) (evk : Fin P.columns → Ciphertext P) {k : ℕ}
    (Cc : DAGCircuit k) (cts : Fin k → Ciphertext P) : fheEvalA P evk Cc cts = fheEval P evk Cc cts := by
  rw [fheEvalA, bootGateA_eq, fheEval_eq]
/-! #### Strict leveled evaluators (probe-local; proved equal to the library definitions) -/

/-- `levelGate` with `bootGateA`. -/
def levelGateA (P : Parameters) {L : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P) (δ : ℕ)
    (g : DAGGate) (cts : List (Ciphertext P)) : Ciphertext P :=
  if h : δ - 1 < L then bootGateA P (lk ⟨δ - 1, h⟩) g cts else 0

theorem levelGateA_eq (P : Parameters) {L : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P) :
    levelGateA P lk = levelGate P lk := by
  funext δ g cts
  by_cases h : δ - 1 < L
  · rw [levelGate_of_lt P lk δ g cts h, levelGateA, dif_pos h, bootGateA_eq]
  · rw [levelGate_of_le P lk δ g cts (Nat.le_of_not_lt h), levelGateA, dif_neg h]

/-- `leveledEval` with `levelGateA`. -/
def leveledEvalA (P : Parameters) {L k : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (Cc : DAGCircuit (k + k)) (cts : Fin (k + k) → Ciphertext P) : Ciphertext P :=
  (runWith (fun g vs => levelGateA P lk (Cc.depthAt vs.length) g vs) Cc.gates
    (List.ofFn cts)).getD Cc.output 0

theorem leveledEvalA_eq (P : Parameters) {L k : ℕ} (lk : Fin L → Fin P.columns → Ciphertext P)
    (Cc : DAGCircuit (k + k)) (cts : Fin (k + k) → Ciphertext P) :
    leveledEvalA P lk Cc cts = leveledEval P lk Cc cts := by
  rw [leveledEvalA, levelGateA_eq, leveledEval_eq]

/-- `leveledEvalCircuit` with `leveledEvalA`. -/
def leveledEvalCircuitA (P : Parameters) {L k : ℕ} [NeZero k]
    (lk : Fin L → Fin P.columns → Ciphertext P) (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) : Ciphertext P :=
  leveledEvalA P lk (Cc.toNANDForm hC).layerNAND (literalCts P cts)

theorem leveledEvalCircuitA_eq (P : Parameters) {L k : ℕ} [NeZero k]
    (lk : Fin L → Fin P.columns → Ciphertext P) (Cc : DAGCircuit k)
    (hC : ∀ g ∈ Cc.gates, g.args.length ≤ 2) (cts : Fin k → Ciphertext P) :
    leveledEvalCircuitA P lk Cc hC cts = leveledEvalCircuit P lk Cc hC cts := by
  rw [leveledEvalCircuitA, leveledEvalA_eq, leveledEvalCircuit_eq]

abbrev A0 : Parameters := ⟨⟨0, 2, 2, by decide⟩, 1, by decide⟩
def enc0 (P : Parameters) (b : ℤ) : Ciphertext P := (b : ZMod P.lwe.modulus) • gadget P
def s0 : Secret A0 := fun i => i.elim0
def lk (L : ℕ) : Fin L → Fin A0.columns → Ciphertext A0 :=
  levelKey A0 (fun _ => (0, 0)) (fun _ => s0) (fun _ _ _ _ => true)

def xorC : DAGCircuit 2 where
  gates := [⟨.not, [0, 1]⟩, ⟨.not, [0, 2]⟩, ⟨.not, [1, 2]⟩, ⟨.not, [3, 4]⟩]
  output := 5
  args_lt := by decide
  output_lt := by decide

def oddC : DAGCircuit 2 where
  gates := [⟨.not, [1]⟩, ⟨.not, [2]⟩, ⟨.not, [0, 3]⟩]
  output := 4
  args_lt := by decide
  output_lt := by decide

/-- `NAND(x₀, NAND(x₁))`: the smallest NAND-form circuit whose layering needs a parity twin (`x₀`,
at level 0, is read by a level-2 gate). -/
def twoC : DAGCircuit 2 where
  gates := [⟨.not, [1]⟩, ⟨.not, [0, 2]⟩]
  output := 3
  args_lt := by decide
  output_lt := by decide

def twoL : DAGCircuit (2 + 2) := ⟨twoC.layerGates, twoC.layerOutput, by decide, by decide⟩
theorem twoL_eq : twoL = twoC.layerNAND := rfl
theorem twoL_ok : twoL.IsLayered ∧ twoL.IsNANDForm ∧ twoL.depth = 2 ∧ ¬ twoC.IsLayered := by
  decide

/-- `AND(x₀, x₁)`: one fan-in-2 `∧` gate. -/
def andC : DAGCircuit 2 where
  gates := [⟨.and, [0, 1]⟩]
  output := 2
  args_lt := by decide
  output_lt := by decide

theorem andC_fanin : ∀ g ∈ andC.gates, g.args.length ≤ 2 := by decide

/-- The layered circuits rebuilt from `layerGates`/`layerOutput` (the data of `layerNAND`) with their
fields proved by `decide` on the instance (as 6a's probe P9 does), so the leveled run does not depend
on the admitted fields N12–N13; `xorL_eq`/`oddL_eq` show they are `layerNAND`'s circuits. -/
def xorL : DAGCircuit (2 + 2) := ⟨xorC.layerGates, xorC.layerOutput, by decide, by decide⟩
def oddL : DAGCircuit (2 + 2) := ⟨oddC.layerGates, oddC.layerOutput, by decide, by decide⟩

theorem xorL_eq : xorL = xorC.layerNAND := rfl
theorem oddL_eq : oddL = oddC.layerNAND := rfl

theorem xorL_ok : xorL.IsLayered ∧ xorL.IsNANDForm ∧ xorL.depth = 3 := by
  decide
theorem oddL_ok : oddL.IsLayered ∧ oddL.IsNANDForm ∧ oddL.depth = 3 := by
  decide

def inp (a b : Bool) : Fin 2 → Bool := fun i => if i.val = 0 then a else b

def logp (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/ev/probes/P6b_LeveledCircuits.progress" .append
  h.putStrLn s; h.flush

end P6

open P6 in
#eval (twoL.gates, twoL.output, xorL.gates.length, oddL.gates.length)

open P6 in
#eval show IO Unit from do
  logp "P6b start (twoC layered, all inputs)"
  let mut out : List String := []
  for (a, b) in [(false, false), (true, false), (false, true), (true, true)] do
    let x := inp a b
    let r := leveledEvalA (L := 2) A0 (lk 2) twoL (literalCts A0 fun j => enc0 A0 (x j).toNat)
    let line := s!"twoC layered x=({a},{b}): gates {twoL.gates.length}, depth {twoL.depth}, " ++
      s!"C.eval {twoC.eval x}, L.eval (litInput x) {twoL.eval (litInput x)}, output = (C.eval)•G: " ++
      s!"{decide (r = enc0 A0 (twoC.eval x).toNat)}, decrypt = {decrypt A0 s0 r}"
    logp line
    out := out ++ [line]
  IO.println (String.intercalate "\n" out)
#print axioms P6.leveledEvalA_eq
#print axioms P6.twoL_ok
#print axioms P6.twoL_eq
