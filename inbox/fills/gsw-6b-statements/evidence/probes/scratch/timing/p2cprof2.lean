import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme

/-! Probe P2c (gsw-6b statements, check 7): `homEvalFormula` (G3), `#eval` (evidence, not
proof: `barrington` is well-founded recursion, which the kernel does not reduce).
* `q = 5`, `n = 1`, `m = 2`, `ℓ = 3` (`N = 6`): depth-2 formulas (XOR as `(x₀ ∨ x₁) ∧ (¬x₀ ∨ ¬x₁)`
  and as `(x₀ ∧ ¬x₁) ∨ (¬x₀ ∧ x₁)`), depth-1 `∧`, `∨`, a fan-in-1 node and both constants, on
  every input, noise-free inputs `x j • G`: the tuple printed is
  `(c.eval x, homEvalFormula = (c.eval x)•G, coordinate 0 = (!c.eval x)•G,
  every other coordinate is 0, decrypt under s = 2 of homEvalFormula = c.eval x)`.
* `q = 65536`, `ℓ = 16` (`N = 32`), key `t = (−3, 1)`, input errors `±1` (`β = 1`): the noise of
  the inputs, the observed noise of `homEvalFormula` as an encryption of `c.eval x`, G3's bound
  `4^depth·(2·(N·β))` and `q/2`, for both depth-2 XOR formulas on every input.
-/

open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open BoolCircuit BranchingProgram

namespace P2

abbrev TP (q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : Parameters := ⟨⟨1, 2, q, hq⟩, ℓ, hℓ⟩
abbrev P5 : Parameters := TP 5 3 (by decide) (by decide)

def enc0 (P : Parameters) (b : ℤ) : Ciphertext P := (b : ZMod P.lwe.modulus) • gadget P

/-- Width-3 program on 2 inputs: `⟨x₀: id | +1⟩, ⟨x₁: +1 | +2⟩, ⟨x₀: +2 | id⟩`. -/
def B3 : BranchingProgram 3 2 :=
  ⟨[⟨0, id, fun i => i + 1⟩, ⟨1, fun i => i + 1, fun i => i + 2⟩, ⟨0, fun i => i + 2, id⟩]⟩

theorem B3_perm : B3.IsPermutation := by decide
theorem B3_length : B3.length = 3 := by decide

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

/-- The function state of nested arrays (default `0` out of range). -/
def ofArr (P : Parameters) {w : ℕ} (A : Array (Array (Array (ZMod P.lwe.modulus)))) :
    Fin w → Ciphertext P :=
  fun k i j => ((A.getD k.val #[]).getD i.val #[]).getD j.val 0

theorem ofArr_toArr (P : Parameters) {w : ℕ} (V : Fin w → Ciphertext P) :
    ofArr P (toArr P V) = V := by
  funext k i j
  simp [ofArr, toArr, Array.getD_eq_getD_getElem?]

/-- `homEvalPBP`'s fold over a strict array accumulator. -/
def evalA (P : Parameters) {w k : ℕ} (B : BranchingProgram w k) (cts : Fin k → Ciphertext P)
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

/-! ### P2c: formulas, `#eval` -/

def x0 : TreeCircuit 2 := .lit ⟨0, true⟩
def x1 : TreeCircuit 2 := .lit ⟨1, true⟩
def nx0 : TreeCircuit 2 := .lit ⟨0, false⟩
def nx1 : TreeCircuit 2 := .lit ⟨1, false⟩

def formulas : List (String × TreeCircuit 2) :=
  [("xor = (x0 ∨ x1) ∧ (¬x0 ∨ ¬x1)", .node true [.node false [x0, x1], .node false [nx0, nx1]]),
   ("xor = (x0 ∧ ¬x1) ∨ (¬x0 ∧ x1)", .node false [.node true [x0, nx1], .node true [nx0, x1]]),
   ("x0 ∧ x1", .node true [x0, x1]),
   ("x0 ∨ ¬x1", .node false [x0, nx1]),
   ("fan-in 1: ∧[¬x1]", .node true [nx1]),
   ("true", .node true []),
   ("false", .node false [])]

def inputs : List (Fin 2 → Bool) :=
  [![false, false], ![true, false], ![false, true], ![true, true]]

def sec : Fin 1 → ZMod 5 := fun _ => 2

/-- For one formula and input: (value, coordinate `σ 0` = value•G, coordinate `0` =
(¬value)•G, other coordinates `0`, decrypt of `homEvalFormula` = value). -/
def checkFormula (c : TreeCircuit 2) (x : Fin 2 → Bool) : Bool × Bool × Bool × Bool × Bool :=
  let cts := fun j => enc0 P5 (x j).toNat
  let st : Fin 5 → Ciphertext P5 :=
    ofArr P5 (evalA P5 (barrington c sigma1) cts (Pi.single 0 (gadget P5)))
  let out := formulaA P5 c cts
  (c.eval x,
   decide (out = enc0 P5 (c.eval x).toNat),
   decide (st 0 = enc0 P5 (!c.eval x).toNat),
   (List.finRange 5).all (fun i => i = 0 || i = sigma1 0 || decide (st i = 0)),
   decrypt P5 sec out == c.eval x)

def err (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ)
    (C : Ciphertext P) : Fin P.columns → ℤ :=
  fun j => (Matrix.vecMul t C j - (x : ZMod P.lwe.modulus) * Matrix.vecMul t (gadget P) j).valMinAbs

/-! ### P2d: G3's noise bound, `#eval` -/

abbrev Q16 : Parameters := TP 65536 16 (by decide) (by decide)
def t16 : Fin 2 → ZMod 65536 := secretVector Q16 (fun _ => 3)
def mk16 (b : ℤ) (r : Fin Q16.columns → ℕ) (e : Fin Q16.columns → ℤ) : Ciphertext Q16 :=
  fun i j => enc0 Q16 b i j +
    if i.val = 0 then ((r j : ℤ) : ZMod 65536) else ((e j + 3 * r j : ℤ) : ZMod 65536)
def r16 : Fin Q16.columns → ℕ := fun j => (4099 * j.val + 17) % 65536
def e16 : Fin 2 → Fin Q16.columns → ℤ := fun k j => if (j.val + 2 * k.val) % 3 = 0 then 1 else -1
def noise16 (x : ℤ) (C : Ciphertext Q16) : ℕ :=
  (List.ofFn fun j => (err Q16 t16 x C j).natAbs).foldl max 0


def logp (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/ev/probes/scratch/p2c.progress" .append
  h.putStrLn s; h.flush
end P2
def show' (P : Parameters) (M : Ciphertext P) : List (List ℕ) :=
  List.ofFn fun i => List.ofFn fun j => (M i j).val
open P2 in
#eval show IO Unit from do
  logp "start2"
  let c : TreeCircuit 2 := .node true [.node false [x0, x1], .node false [nx0, nx1]]
  let x : Fin 2 → Bool := ![true, true]
  let cts := fun j => enc0 P5 (x j).toNat
  logp s!"eval {c.eval x}"
  let st : Fin 5 → Ciphertext P5 := ofArr P5 (evalA P5 (barrington c sigma1) cts (Pi.single 0 (gadget P5)))
  logp s!"st0 {show' P5 (st 0)}"
  logp s!"st1 {show' P5 (st 1)}"
  let out := formulaA P5 c cts
  logp s!"out {show' P5 out}"
  logp s!"eq {decide (out = enc0 P5 (c.eval x).toNat)}"
  logp s!"st0eq {decide (st 0 = enc0 P5 (!c.eval x).toNat)}"
  logp s!"all {(List.finRange 5).all (fun i => i = 0 || i = sigma1 0 || decide (st i = 0))}"
  logp s!"dec {decrypt P5 sec out}"
