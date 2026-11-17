import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Bootstrap
open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW BoolCircuit BranchingProgram
namespace T
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

/-- `homEvalFormula` through `evalA`. -/
def formulaA (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) : Ciphertext P :=
  ofArr P (w := 5) (evalA P (barrington c sigma1) (fun j => matA P (cts j)) (Pi.single 0 (gadget P)))
    (sigma1 0)

theorem formulaA_eq (P : Parameters) {k : ℕ} [NeZero k] (c : TreeCircuit k)
    (cts : Fin k → Ciphertext P) : formulaA P c cts = homEvalFormula P c cts := by
  have h : (fun j => matA P (cts j)) = cts := funext fun j => matA_eq P (cts j)
  rw [formulaA, h, evalA_eq, homEvalFormula_eq]
def enc0 (P : Parameters) (b : ℤ) : Ciphertext P := (b : ZMod P.lwe.modulus) • gadget P
abbrev A0 : Parameters := ⟨⟨0, 2, 2, by decide⟩, 1, by decide⟩
abbrev B1 : Parameters := ⟨⟨1, 2, 2, by decide⟩, 1, by decide⟩
def logp (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/ev/probes/scratch/boot.progress" .append
  h.putStrLn s; h.flush
def show' (P : Parameters) (M : Ciphertext P) : List (List ℕ) :=
  List.ofFn fun i => List.ofFn fun j => (M i j).val
end T
open T in
#eval show IO Unit from do
  logp "start"
  let c := nandFormula A0 (gadget A0) (gadget A0)
  let t0 ← IO.monoMsNow
  let L := (barrington c sigma1).length
  logp s!"A0 depth {c.depth} len {L} {(← IO.monoMsNow) - t0}ms"
  let t0 ← IO.monoMsNow
  let evk : Fin A0.columns → Ciphertext A0 := fun i => enc0 A0 (keyBits A0 (fun _ => 0) i).toNat
  let r := show' A0 (formulaA A0 c evk)
  let s := toString r
  logp s!"A0 bootNAND(G,G) {s} {(← IO.monoMsNow) - t0}ms"
  let c := nandFormula B1 (gadget B1) (gadget B1)
  let t0 ← IO.monoMsNow
  let L := (barrington c sigma1).length
  logp s!"B1 depth {c.depth} len {L} {(← IO.monoMsNow) - t0}ms"
