import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Branching
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Scheme

/-! Probe P2b (gsw-6b statements, check 7): G2 (`encrypts_homEvalPBP`) with noise.
`n = 1`, `m = 2`, `ℓ = 8`, `q = 256` (`N = 16`), key `t = (−3, 1)`: inputs with explicit errors
`±1` (`β = 1`); G2's conclusion with noise `B3.length·(2·(N·β)) = 96 < 128` for every input and
coordinate, start `0`: the witness check `checkB` (sound by `encrypts_of_check`) evaluated by `#eval` on
the strict evaluator `evalA` (proved equal to `homEvalPBP`), with the observed noise; the inputs' own
check by kernel `decide`. (A first version proved G2's conclusion here by kernel `decide`; it ran out of
memory, 13 GB, and was dropped: `P2b_kernel_attempt.out`.) -/

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

/-- Bijectivity of a map `Fin 3 → Fin 3` from injectivity (finite type), decided pointwise. -/
theorem bij3 (f : Fin 3 → Fin 3) (h : ∀ a b, f a = f b → a = b) : Function.Bijective f :=
  (Finite.injective_iff_bijective).1 fun a b => h a b

theorem B3_perm : B3.IsPermutation := by
  intro ι hι
  simp only [B3, List.mem_cons, List.not_mem_nil, or_false] at hι
  rcases hι with rfl | rfl | rfl <;> exact ⟨bij3 _ (by decide), bij3 _ (by decide)⟩
theorem B3_length : B3.length = 3 := by decide

/-! ### P2b: G2 with noise -/

abbrev Q : Parameters := TP 256 8 (by decide) (by decide)
def s : Fin 1 → ZMod 256 := fun _ => 3
def t : Fin 2 → ZMod 256 := secretVector Q s

def mk (b : ℤ) (r : Fin Q.columns → ℕ) (e : Fin Q.columns → ℤ) : Ciphertext Q :=
  fun i j => enc0 Q b i j +
    if i.val = 0 then ((r j : ℤ) : ZMod 256) else ((e j + 3 * r j : ℤ) : ZMod 256)

def err (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ)
    (C : Ciphertext P) : Fin P.columns → ℤ :=
  fun j => (Matrix.vecMul t C j - (x : ZMod P.lwe.modulus) * Matrix.vecMul t (gadget P) j).valMinAbs

def checkB (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ) (β : ℕ)
    (C : Ciphertext P) : Prop := ∀ j, (err P t x C j).natAbs ≤ β

instance (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus) (x : ℤ) (β : ℕ)
    (C : Ciphertext P) : Decidable (checkB P t x β C) := by
  unfold checkB; infer_instance

theorem encrypts_of_check (P : Parameters) (t : Fin (P.lwe.dimension + 1) → ZMod P.lwe.modulus)
    (x : ℤ) (β : ℕ) (C : Ciphertext P) (h : checkB P t x β C) : Encrypts P t x β C := by
  rw [encrypts_iff]
  refine ⟨err P t x C, h, ?_⟩
  funext j
  simp only [err, Pi.add_apply, Pi.smul_apply, smul_eq_mul, ZMod.coe_valMinAbs]
  ring

def r0 : Fin Q.columns → ℕ := fun j => (37 * j.val + 11) % 256
def eA : Fin 2 → Fin Q.columns → ℤ := fun k j => if (j.val + k.val) % 2 = 0 then 1 else -1

/-- The inputs: bit `x j` with error `eA j` (`β = 1`). -/
def cts (x : Fin 2 → Bool) : Fin 2 → Ciphertext Q := fun j => mk (x j).toNat r0 (eA j)

theorem g2_inputs : ∀ (x : Fin 2 → Bool) (j : Fin 2), checkB Q t (x j).toNat 1 (cts x j) := by
  decide +kernel

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

/-- G2's conclusion as a Boolean check on the strict evaluation (`evalA_eq` makes it the library's
`homEvalPBP`), with the observed maximal noise. -/
def g2Check (x : Fin 2 → Bool) (i : Fin 3) : Bool × ℕ × ℕ :=
  let C := (ofArr Q (evalA Q B3 (cts x) (Pi.single 0 (gadget Q))) i : Ciphertext Q)
  let msg : ℤ := (decide (B3.yield x 0 = i)).toNat
  (decide (checkB Q t msg (B3.length * (2 * (Q.columns * 1))) C),
   (List.ofFn fun j => (err Q t msg C j).natAbs).foldl max 0, B3.length * (2 * (Q.columns * 1)))

end P2

open P2 in
#eval ([![false, false], ![true, false], ![false, true], ![true, true]] : List (Fin 2 → Bool)).map
  fun x => ((x 0, x 1), (List.finRange 3).map fun i => g2Check x i)
#print axioms P2.evalA_eq
#print axioms P2.g2_inputs
