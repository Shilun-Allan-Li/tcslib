import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Leveled

/-! Probe P6a (gsw-6b statements, check 7): the leveled key chain with **distinct** keys.
Parameters `B1 = (n = 1, m = 2, q = 2, ℓ = 1)` (`N = 2`), the smallest with distinct secrets.
A bootstrapped gate there is Barrington's program of 196,096 instructions; one `bootNAND` did not
finish in 29 minutes of CPU (`scratch/boot2.lean`, killed), so the full `leveledEval` with distinct
keys is out of reach of `#eval`; this probe checks every other part of a level step with distinct
keys, and P6b runs `leveledEval`/`leveledEvalCircuit` end to end at `n = 0`.
Key chain of `L + 1 = 2` honest **noise-free** keys `pk_d = (A, A s_d + 0)` (`LWE.noisyValues` with
zero errors), `s_0 = 0`, `s_1 = 1`; inputs are genuine encryptions under `pk_0`.
* **P6a.1** (kernel `decide`): `literalCts` — for every input `x`, literal `j` of `literalCts P cts`
  decrypts under `s_0` to `litInput x j`.
* **P6a.2** (kernel `decide`): the level key `levelKey P pks ss R 0` (L1's object) encrypts, under the key
  of level 1, the key bits of level 0: `decrypt P s_1 (levelKey … 0 j) = keyBits P s_0 j` for every `j`.
* **P6a.3** (`#eval`): the message of the level-1 bootstrapped gate `NAND(lit 0, lit 1)`, i.e. the
  augmented formula `nandFormula P (lit 0) (lit 1)` evaluated on the key bits of `s_0` (G7 at level 1),
  equals `NAND` of the literal values for every input; printed also: the inputs decrypted under `s_1`
  and the level key decrypted under `s_0` (to show the keys differ in effect).
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

abbrev B1 : Parameters := ⟨⟨1, 2, 2, by decide⟩, 1, by decide⟩
def A : Matrix (Fin 2) (Fin 1) (ZMod 2) := fun i _ => if i.val = 0 then 1 else 1
def ss : Fin 2 → Secret B1 := fun d _ => if d.val = 0 then 0 else 1
def pks : Fin 2 → PublicKey B1 := fun d => (A, LWE.noisyValues B1.lwe A (ss d) 0)
def Rk : LevelCoins B1 1 := fun _ i a b => (i.val + a.val + b.val) % 2 == 0
def lk : Fin 1 → Fin B1.columns → Ciphertext B1 := levelKey B1 pks ss Rk
def Rin : Fin 2 → Coins B1 := fun j a b => (j.val + 2 * a.val + b.val) % 3 == 0
def cts (x : Fin 2 → Bool) : Fin 2 → Ciphertext B1 := fun j => encrypt B1 (pks 0) (x j) (Rin j)

theorem literal_ok : ∀ (x : Fin 2 → Bool) (j : Fin (2 + 2)),
    decrypt B1 (ss 0) (literalCts B1 (cts x) j) = litInput x j := by
  decide +kernel

theorem levelKey_ok : ∀ j : Fin B1.columns, decrypt B1 (ss 1) (lk 0 j) = keyBits B1 (ss 0) j := by
  decide +kernel

def logp (s : String) : IO Unit := do
  let h ← IO.FS.Handle.mk "/home/user/ev/probes/P6a_LeveledKeys.progress" .append
  h.putStrLn s; h.flush

end P6

open P6 in
#eval show IO Unit from do
  logp "P6a start"
  let mut out : List String := []
  for x in [![false, false], ![true, false], ![false, true], ![true, true]] do
    let lc := literalCts B1 (cts x)
    let m := (nandFormula B1 (lc 0) (lc 1)).eval (keyBits B1 (ss 0))
    let line := s!"x=({x 0},{x 1}): nandFormula(lit0, lit1) on keyBits s_0 = {m}, " ++
      s!"NAND(x0, x1) = {!(x 0 && x 1)}; inputs under s_1 = " ++
      s!"({decrypt B1 (ss 1) (cts x 0)},{decrypt B1 (ss 1) (cts x 1)})"
    logp line
    out := out ++ [line]
  let line := s!"level key under s_0: {(List.finRange B1.columns).map fun j => decrypt B1 (ss 0) (lk 0 j)}, " ++
    s!"under s_1: {(List.finRange B1.columns).map fun j => decrypt B1 (ss 1) (lk 0 j)}, " ++
    s!"keyBits s_0: {(List.finRange B1.columns).map fun j => keyBits B1 (ss 0) j}, " ++
    s!"keyBits s_1: {(List.finRange B1.columns).map fun j => keyBits B1 (ss 1) j}"
  logp line
  out := out ++ [line]
  IO.println (String.intercalate "\n" out)
#print axioms P6.literal_ok
#print axioms P6.levelKey_ok
