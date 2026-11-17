import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme
open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW BoolCircuit BranchingProgram
abbrev TP (q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : Parameters := ⟨⟨1, 2, q, hq⟩, ℓ, hℓ⟩
abbrev P5 : Parameters := TP 5 3 (by decide) (by decide)
def enc0 (P : Parameters) (b : ℤ) : Ciphertext P := (b : ZMod P.lwe.modulus) • gadget P
def mat (P : Parameters) (M : Ciphertext P) : Ciphertext P :=
  let a := Array.ofFn fun i => Array.ofFn fun j => M i j
  fun i j => (a[i.val]'(by simp [a]))[j.val]'(by simp [a])
def matV (P : Parameters) {w : ℕ} (V : Fin w → Ciphertext P) : Fin w → Ciphertext P :=
  let a := Array.ofFn fun k => mat P (V k)
  fun k => a[k.val]'(by simp [a])
def evalM (P : Parameters) {w k : ℕ} (B : BranchingProgram w k) (cts : Fin k → Ciphertext P)
    (V : Fin w → Ciphertext P) : Fin w → Ciphertext P :=
  B.instrs.foldl (fun U ι => matV P (ι.stepWith (select P) cts U)) (matV P V)
def x0 : TreeCircuit 2 := .lit ⟨0, true⟩
def x1 : TreeCircuit 2 := .lit ⟨1, true⟩
def c1 : TreeCircuit 2 := .node true [x0, x1]
def show' (P : Parameters) (M : Ciphertext P) : List (List ℕ) :=
  List.ofFn fun i => List.ofFn fun j => (M i j).val
def tm (s : String) (f : Unit → List (List ℕ)) : IO Unit := do
  let t0 ← IO.monoMsNow
  let r := f ()
  IO.println s!"{s} {r} {(← IO.monoMsNow) - t0}ms"
#eval tm "len" fun _ => [[(barrington c1 sigma1).length]]
#eval tm "select" fun _ => show' P5 (select P5 (gadget P5) (gadget P5) (gadget P5))
#eval tm "evalM c1" fun _ => show' P5 (evalM P5 (barrington c1 sigma1) (fun _ => gadget P5) (Pi.single 0 (gadget P5)) (sigma1 0))
#eval tm "homEvalPBP c1" fun _ => show' P5 (homEvalPBP P5 (barrington c1 sigma1) (fun _ => gadget P5) (Pi.single 0 (gadget P5)) (sigma1 0))
#eval tm "len" fun _ => [[(barrington c1 sigma1).length]]
