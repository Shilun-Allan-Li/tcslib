import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW BoolCircuit BranchingProgram
abbrev TP (q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : Parameters := ⟨⟨1, 2, q, hq⟩, ℓ, hℓ⟩
abbrev P5 : Parameters := TP 5 3 (by decide) (by decide)
def enc0 (P : Parameters) (b : ℤ) : Ciphertext P := (b : ZMod P.lwe.modulus) • gadget P
/-! #### Materializing evaluator (probe-local; proved equal to the library definitions)
The library's `homEvalPBP` folds closures, so `#eval` recomputes every earlier state on each
access (exponential in the program length). `evalM` is the same fold with every state
materialized into arrays after each step; `evalM_eq` proves it equal to `homEvalPBP` through the
readers `homEvalPBP_eq` and `BranchingProgram.evalWith_eq`, so `#eval` of `evalM` evaluates
`homEvalPBP` itself, and `formulaM_eq` does the same for `homEvalFormula`. -/

/-- A matrix with its entries computed once into an array. -/
def mat (P : Parameters) (M : Ciphertext P) : Ciphertext P :=
  let a := Array.ofFn fun i => Array.ofFn fun j => M i j
  fun i j => (a[i.val]'(by simp only [a, Array.size_ofFn]; exact i.isLt))[j.val]'(by
    simp only [a, Array.getElem_ofFn, Array.size_ofFn]; exact j.isLt)

theorem mat_eq (P : Parameters) (M : Ciphertext P) : mat P M = M := by
  funext i j; simp only [mat, Array.getElem_ofFn]

/-- A state vector with every coordinate materialized. -/
def matV (P : Parameters) {w : ℕ} (V : Fin w → Ciphertext P) : Fin w → Ciphertext P :=
  let a := Array.ofFn fun k => mat P (V k)
  fun k => a[k.val]'(by simp only [a, Array.size_ofFn]; exact k.isLt)

theorem matV_eq (P : Parameters) {w : ℕ} (V : Fin w → Ciphertext P) : matV P V = V := by
  funext k; simp only [matV, Array.getElem_ofFn, mat_eq]

/-- `homEvalPBP`'s fold with materialization after each step. -/
def evalM (P : Parameters) {w k : ℕ} (B : BranchingProgram w k) (cts : Fin k → Ciphertext P)
    (V : Fin w → Ciphertext P) : Fin w → Ciphertext P :=
  B.instrs.foldl (fun U ι => matV P (ι.stepWith (select P) cts U)) (matV P V)

theorem evalM_eq (P : Parameters) {w k : ℕ} (B : BranchingProgram w k)
    (cts : Fin k → Ciphertext P) (V : Fin w → Ciphertext P) :
    evalM P B cts V = homEvalPBP P B cts V := by
  rw [homEvalPBP_eq, BranchingProgram.evalWith_eq]
  simp only [evalM, matV_eq]

def x0 : TreeCircuit 2 := .lit ⟨0, true⟩
def x1 : TreeCircuit 2 := .lit ⟨1, true⟩
def c1 : TreeCircuit 2 := .node true [x0, x1]
def show' (P : Parameters) (M : Ciphertext P) : List (List ℕ) :=
  List.ofFn fun i => List.ofFn fun j => (M i j).val
def tm (s : String) (f : Unit → List (List ℕ)) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{s} {r} {(← IO.monoMsNow) - t0}ms"
abbrev P2 : Parameters := ⟨⟨0, 2, 4, by decide⟩, 2, by decide⟩
def BB : BranchingProgram 5 2 := ⟨[Instr.ofPerm (0:Fin 2) 1 sigma1, Instr.ofPerm (0:Fin 2) 1 sigma1]⟩
#eval tm "L2" fun _ => show' P2 (evalM P2 BB (fun _ => gadget P2) (Pi.single 0 (gadget P2)) 0)
