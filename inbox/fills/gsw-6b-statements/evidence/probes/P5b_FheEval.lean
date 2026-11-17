import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap

/-! Probe P5b (gsw-6b statements, check 7): `fheEval` (G10), noise-free, `#eval`.
At `A0 = (n = 0, m = 2, q = 2, ℓ = 1)` with the evaluation key and strict evaluators of P5
(`P5_Bootstrap.lean`; `fheEvalA_eq` proves `fheEvalA = fheEval` through `fheEval_eq` and the three
`bootGate` case readers). Circuit `xorPad` (the lead's reduced order): XOR in NAND form (4 fan-in-2
gates) plus one **fan-in-0** gate `NAND[]` (padded to `(G, G)`) and one **fan-in-1** gate `NAND[v5]`
(padded to `(a, a)`, the output: XNOR); NAND form by `decide`. Inputs `x j • G`; for each input, the
output equals `(Cc.eval x) • G` and decrypts to `Cc.eval x`. Each bootstrapped gate is ≈ 2–3 minutes of
`#eval`, so the run is capped at 25 minutes (`tools/probe/run_capped.sh`); the inputs evaluated before
the cap are in `P5b_FheEval.progress`. -/

open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit BranchingProgram

namespace P5
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

abbrev A0 : Parameters := ⟨⟨0, 2, 2, by decide⟩, 1, by decide⟩
def enc0 (P : Parameters) (b : ℤ) : Ciphertext P := (b : ZMod P.lwe.modulus) • gadget P
def s0 : Fin 0 → ZMod 2 := fun i => i.elim0
/-- The honest noise-free public key at `n = 0`: `A` empty, `b = A s + 0 = 0`. -/
def pk0 : PublicKey A0 := (0, 0)
def R0 : Fin A0.columns → Coins A0 := fun _ _ _ => true
/-- The evaluation key: `evalKey` of the honest noise-free key. -/
def evk0 : Fin A0.columns → Ciphertext A0 := evalKey A0 pk0 s0 R0

def xorC : DAGCircuit 2 where
  gates := [⟨.not, [0, 1]⟩, ⟨.not, [0, 2]⟩, ⟨.not, [1, 2]⟩, ⟨.not, [3, 4]⟩]
  output := 5
  args_lt := by decide
  output_lt := by decide

def zeroC : DAGCircuit 2 where
  gates := [⟨.not, []⟩, ⟨.not, [0]⟩, ⟨.not, [3]⟩, ⟨.not, [2, 4]⟩]
  output := 5
  args_lt := by decide
  output_lt := by decide

/-- XOR in NAND form plus one fan-in-0 gate `v6 = NAND[]` and one fan-in-1 gate `v7 = NAND[v5]`
(output, XNOR): the reduced circuit of the lead's order. -/
def xorPad : DAGCircuit 2 where
  gates := [⟨.not, [0, 1]⟩, ⟨.not, [0, 2]⟩, ⟨.not, [1, 2]⟩, ⟨.not, [3, 4]⟩, ⟨.not, []⟩, ⟨.not, [5]⟩]
  output := 7
  args_lt := by decide
  output_lt := by decide

theorem xorPad_nand : xorPad.IsNANDForm := by decide
theorem xorC_nand : xorC.IsNANDForm := by decide
theorem zeroC_nand : zeroC.IsNANDForm := by decide

def inp (a b : Bool) : Fin 2 → Bool := fun i => if i.val = 0 then a else b

def logp (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/ev/probes/P5b_FheEval.progress" .append
  h.putStrLn s; h.flush

end P5

open P5 in
#eval show IO Unit from do
  logp "P5b start (xorPad: 6 gates incl. fan-in 0 and fan-in 1)"
  let mut out : List String := []
  for (a, b) in [(true, false), (true, true), (false, false), (false, true)] do
    let x := inp a b
    let r := fheEvalA A0 evk0 xorPad (fun j => enc0 A0 (x j).toNat)
    let line := s!"fheEval xorPad x=({a},{b}): eval {xorPad.eval x}, output = (eval)•G: " ++
      s!"{decide (r = enc0 A0 (xorPad.eval x).toNat)}, decrypt = {decrypt A0 s0 r}"
    logp line
    out := out ++ [line]
  IO.println (String.intercalate "\n" out)
#print axioms P5.fheEvalA_eq
#print axioms P5.xorPad_nand
