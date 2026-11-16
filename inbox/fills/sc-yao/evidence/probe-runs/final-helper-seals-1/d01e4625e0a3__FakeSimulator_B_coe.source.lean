/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeMessage
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobSimulator
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut requested := 0
  let mut excluded := 0
  for (name, ci) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let home := env.header.moduleNames[idx.toNat]!
      if home.toString.startsWith "TCSlib." then
        if let .defnInfo d := ci then
          let status ← liftCoreM <| Lean.getReducibilityStatus name
          let matcher := Lean.Meta.isMatcherCore env name
          let rec body : Nat → Expr → Expr
            | 0, e => e
            | fuel+1, .lam _ _ b _ => body fuel b
            | fuel+1, .letE _ _ v b _ => body fuel (b.instantiate1 v)
            | _, e => e
          let ty := d.type.getForallBody.getAppFn.constName?
          let val := body 64 d.value
          let coe := ty == some `CoeFun || ty == some `Coe
          let map := if val.getAppArgs.isEmpty then val else val.getAppArgs.back!
          let projection := match (body 64 map).getAppFn with
            | .proj .. => true
            | .const n _ => env.isProjectionFn n
            | _ => false
          let isNotation : Bool := (name == `Complexity.PolyExpr.eval && false) ||
            (true && coe && projection)
          if isNotation || (status == .reducible && !matcher) then
            excluded := excluded + 1
            logInfo m!"EXCLUDED\t{home}\t{name}"
          else
            let id := mkIdent name
            if status != .irreducible then
              elabCommand (← `(command| attribute [local irreducible] $id:ident))
            let installed ← liftCoreM <| Lean.getReducibilityStatus name
            unless installed == .irreducible do
              throwError "seal not installed: {name}"
            requested := requested + 1
            logInfo m!"SEALED\t{home}\t{name}"
  logInfo m!"SEAL_COUNTS requested={requested} excluded={excluded}"

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A fixed uniform Bob simulator from circuit and seed readers

The data specify polynomial circuit counts, a uniform unary description generator, and
an addressed seed family on arbitrary coin words. The actual fake message and active-answer
leaves are derived, rather than assumed polynomial-time. The existing Bob simulator then
supplies one fixed machine before any input or distinguisher is chosen.

## Main definitions

* `FakeSimulator.Data`: the circuit, algorithm, polynomial, and seed-reader interface.
* `messageAt`, `answersAt`: the actual fake message and active answers at a parameter/tape.
* `message`, `answers`: their total canonical-layout adapters.
* `simulator`: the existing Bob simulator instantiated by these proved leaves.

## Main results

* `message_poly`, `answers_poly`: actual polynomial-time leaves derived from the data.
* `simulator_uniform`, `simulator_coins`: one fixed uniform machine and its coin polynomial.
* `simulator_runAtL`, `simulator_runAt`, `idealB_eq`: actual simulated-view endpoints.
* `messageAt_ofFn`: exact typed prescribed-output bits without padding.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (one efficient Bob simulator before the distinguisher).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator

open Complexity Turing BoolCircuit TCSlib.Cryptography.EncodingMachines

/-- The total raw security parameter is the length of the canonical parameter field:
`parameter z = (NUPPT.inParam z).length`. -/
def parameter (z : List Bool) : ℕ := (NUPPT.inParam z).length

/-- `parameter z = (NUPPT.inParam z).length`. -/
theorem parameter_eq (z : List Bool) : parameter z = (NUPPT.inParam z).length := rfl

/-- On the canonical layout with common input `1^n`, `parameter` is exactly `n`. -/
theorem parameter_layout (n : ℕ) (arg advice coins : List Bool) :
    parameter (NUPPT.layout (List.replicate n true) arg advice coins) = n := by
  rw [parameter_eq, NUPPT.inParam_layout, List.length_replicate]

/-- Simulator data consist of polynomial counts and bound, polynomial-time encryption
algorithms and unary description generator, a circuit/output family, and seed key/nonce/XOR
readers on every raw tape. The seed depends only on the parameter and tape.
[PS10, Theorem 163.7] -/
structure Data where
  /-- The two special-encryption evaluation maps. -/
  E₁ : List Bool → List Bool
  E₂ : List Bool → List Bool
  /-- Both encryption evaluation maps are polynomial-time on every word. -/
  E₁_poly : PolyTimeComputable E₁
  E₂_poly : PolyTimeComputable E₂
  /-- Polynomial wire bound and input/output counts. -/
  bound : PolyExpr
  inputs : PolyExpr
  inA : PolyExpr
  inB : PolyExpr
  outLen : PolyExpr
  /-- The polynomial-time generator is called on a normalized unary parameter. -/
  gen : List Bool → List Bool
  gen_poly : PolyTimeComputable gen
  /-- The circuit and its ordered output vertices at each parameter. -/
  circuit : ∀ n, DAGCircuit (inputs.eval n)
  output : ∀ n, Fin (outLen.eval n) → ℕ
  /-- Unary generation returns the canonical circuit/output-word description. -/
  shape : ∀ n, gen (List.replicate n true) = pairEncode (circuit n).encode
    (BinArith.encWords (List.ofFn fun j => encodeNat (output n j)))
  /-- Alice and Bob's selected input ranges lie inside the circuit inputs. -/
  input_range : ∀ n, inA.eval n + inB.eval n ≤ inputs.eval n
  output_lt : ∀ n j, output n j < (circuit n).size
  fanin : ∀ n (i : Fin (circuit n).gates.length), ((circuit n).gates[i]).args.length ≤ 2
  /-- The padded raw-tape seed family, independent of private inputs and output bits. -/
  seed : ∀ n, List Bool → GarbleSeed (circuit n) (Fin n → Bool)
    ((Fin n → Bool) × (Fin n → Bool))
  /-- A valid vertex's Boolean key is its addressed length-`n` coin block. -/
  key : ∀ n r (v : ℕ), v < (circuit n).size → ∀ b,
    keyAt (circuit n) (seed n r) v b = fun t : Fin n =>
      r.getD ((b.toNat * bound.eval n + v) * n + t) false
  /-- The two row nonces occupy the prescribed consecutive length-`n` blocks. -/
  nonce₀ : ∀ n r (i : Fin (circuit n).gates.length) a t, ((seed n r).2.1 i a).1 t =
    r.getD (2 * bound.eval n * n +
      (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false
  nonce₁ : ∀ n r (i : Fin (circuit n).gates.length) a t, ((seed n r).2.1 i a).2 t =
    r.getD (2 * bound.eval n * n +
      (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false
  /-- The row permutation is the addressed XOR shift. -/
  permutation : ∀ n r (i : Fin (circuit n).gates.length) a t,
    (seed n r).2.2 i a t = xor (a t) (r.getD (10 * bound.eval n * n + 2 * i + t) false)

section Constructor

variable
    (E₁ : List Bool → List Bool)
    (E₂ : List Bool → List Bool)
    (E₁_poly : PolyTimeComputable E₁)
    (E₂_poly : PolyTimeComputable E₂)
    (bound : PolyExpr)
    (inputs : PolyExpr)
    (inA : PolyExpr)
    (inB : PolyExpr)
    (outLen : PolyExpr)
    (gen : List Bool → List Bool)
    (gen_poly : PolyTimeComputable gen)
    (circuit : ∀ n, DAGCircuit (inputs.eval n))
    (output : ∀ n, Fin (outLen.eval n) → ℕ)
    (shape : ∀ n, gen (List.replicate n true) = pairEncode (circuit n).encode
    (BinArith.encWords (List.ofFn fun j => encodeNat (output n j))))
    (input_range : ∀ n, inA.eval n + inB.eval n ≤ inputs.eval n)
    (output_lt : ∀ n j, output n j < (circuit n).size)
    (fanin : ∀ n (i : Fin (circuit n).gates.length), ((circuit n).gates[i]).args.length ≤ 2)
    (seed : ∀ n, List Bool → GarbleSeed (circuit n) (Fin n → Bool)
    ((Fin n → Bool) × (Fin n → Bool)))
    (key : ∀ n r (v : ℕ), v < (circuit n).size → ∀ b,
    keyAt (circuit n) (seed n r) v b = fun t : Fin n =>
      r.getD ((b.toNat * bound.eval n + v) * n + t) false)
    (nonce₀ : ∀ n r (i : Fin (circuit n).gates.length) a t, ((seed n r).2.1 i a).1 t =
    r.getD (2 * bound.eval n * n +
      (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + t) false)
    (nonce₁ : ∀ n r (i : Fin (circuit n).gates.length) a t, ((seed n r).2.1 i a).2 t =
    r.getD (2 * bound.eval n * n +
      (4 * i + (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) * (2 * n) + n + t) false)
    (permutation : ∀ n r (i : Fin (circuit n).gates.length) a t,
    (seed n r).2.2 i a t = xor (a t) (r.getD (10 * bound.eval n * n + 2 * i + t) false))

/-- Store the supplied algorithms, polynomials, circuit/output family and seed readers in
`Data`. Every computational field equals its supplied argument through the generated
non-simp projection readers. The pointwise word readers below expose the dependent fields
together, so downstream consumers need no circuit or seed transport. -/
@[simps (config := { isSimp := false }) E₁ E₂ bound inputs inA inB outLen gen circuit output seed]
def Data.make : Data where
  E₁ := E₁
  E₂ := E₂
  E₁_poly := E₁_poly
  E₂_poly := E₂_poly
  bound := bound
  inputs := inputs
  inA := inA
  inB := inB
  outLen := outLen
  gen := gen
  gen_poly := gen_poly
  circuit := circuit
  output := output
  shape := shape
  input_range := input_range
  output_lt := output_lt
  fanin := fanin
  seed := seed
  key := key
  nonce₀ := nonce₀
  nonce₁ := nonce₁
  permutation := permutation

/-- The normalized raw circuit description is `d.gen (1^(parameter z))`. -/
def description (d : Data) (z : List Bool) : List Bool :=
  d.gen (List.replicate (parameter z) true)

/-- `description d z = d.gen (List.replicate (parameter z) true)`. -/
theorem description_eq (d : Data) (z : List Bool) :
    description d z = d.gen (List.replicate (parameter z) true) := rfl

/-- The actual simulated message at parameter `n`, raw tape `r`, and prescribed output
word `f` is `FakeObjects.message` with seed `d.seed n r` and result bits `f.getD j false`.
[PS10, Theorem 163.7] -/
noncomputable def messageAt (d : Data) (n : ℕ) (r f : List Bool) : List Bool :=
  FakeObjects.message (nestedSpecial d.E₁ d.E₂ n) (d.circuit n) (d.seed n r)
    (d.inA.eval n) (d.outLen.eval n) (d.output n) (fun j => f.getD j false)

/-- `messageAt d n r f` is the canonical encoded fake message on `d.seed n r`, with Alice
count `d.inA(n)`, output vertices `d.output n`, and prescribed bits `f.getD j false`. -/
theorem messageAt_eq (d : Data) (n : ℕ) (r f : List Bool) :
    messageAt d n r f =
      FakeObjects.message (nestedSpecial d.E₁ d.E₂ n) (d.circuit n) (d.seed n r)
        (d.inA.eval n) (d.outLen.eval n) (d.output n) (fun j => f.getD j false) := rfl

/-- The active answer at parameter `n` and tape `r` is the canonical flat vector of
`d.inB(n)` false-key blocks beginning at input vertex `d.inA(n)`. -/
def answersAt (d : Data) (n : ℕ) (r : List Bool) : List Bool :=
  List.ofFn (FakeObjects.activeAnswers (d.circuit n) (d.seed n r)
    (d.inA.eval n) (d.inB.eval n))

/-- `answersAt d n r` is `ofFn (activeAnswers (d.circuit n) (d.seed n r) inA(n) inB(n))`. -/
theorem answersAt_eq (d : Data) (n : ℕ) (r : List Bool) :
    answersAt d n r = List.ofFn (FakeObjects.activeAnswers (d.circuit n) (d.seed n r)
      (d.inA.eval n) (d.inB.eval n)) := rfl

/-- The total fake-message leaf reads only the parameter length, raw tape, and prescribed
output word from the canonical NUPPT fields. -/
noncomputable def message (d : Data) (z : List Bool) : List Bool :=
  messageAt d (parameter z) (NUPPT.inCoins z) (pairSndD (NUPPT.inArg z))

/-- `message d z = messageAt d (parameter z) (inCoins z) (snd (inArg z))`. -/
theorem message_eq (d : Data) (z : List Bool) :
    message d z = messageAt d (parameter z) (NUPPT.inCoins z)
      (pairSndD (NUPPT.inArg z)) := rfl

/-- The total active-answer leaf reads only the parameter length and raw simulator tape. -/
def answers (d : Data) (z : List Bool) : List Bool :=
  answersAt d (parameter z) (NUPPT.inCoins z)

/-- `answers d z = answersAt d (parameter z) (inCoins z)`. -/
theorem answers_eq (d : Data) (z : List Bool) :
    answers d z = answersAt d (parameter z) (NUPPT.inCoins z) := rfl

/-- The unary raw parameter `1^(parameter z)` is polynomial-time computable. -/
theorem parameter_unary_poly :
    PolyTimeComputable fun z => List.replicate (parameter z) true :=
  unaryLength_poly NUPPT.polyTimeComputable_inParam

/-- For every polynomial `p`, the unary value `1^(p(parameter z))` is polynomial-time. -/
theorem eval_unary_poly (p : PolyExpr) :
    PolyTimeComputable fun z => List.replicate (p.eval (parameter z)) true :=
  (polyTimeComputable_unaryPoly p).comp NUPPT.polyTimeComputable_inParam

/-- The normalized unary description map is polynomial-time for every simulator data set. -/
theorem description_poly (d : Data) : PolyTimeComputable (description d) :=
  d.gen_poly.comp parameter_unary_poly

/-- The description at every raw word has the canonical circuit/output encoding at its
parameter length, including when the raw common-input field is malformed. -/
theorem description_shape (d : Data) (z : List Bool) :
    description d z = pairEncode (d.circuit (parameter z)).encode
      (BinArith.encWords (List.ofFn fun j => encodeNat (d.output (parameter z) j))) :=
  d.shape (parameter z)

/-- The actual active-answer leaf is polynomial-time from the polynomial counts and seed
key reader alone; no answer-computability assumption is required. [PS10, Theorem 163.7] -/
theorem answers_poly (d : Data) : PolyTimeComputable (answers d) := by
  simpa only [answers_eq, answersAt_eq] using FakeProgram.activeAnswers_poly
    parameter (fun z => d.bound.eval (parameter z)) (fun z => d.inA.eval (parameter z))
    (fun z => d.inB.eval (parameter z)) (fun z => d.inputs.eval (parameter z)) NUPPT.inCoins
    parameter_unary_poly (eval_unary_poly d.bound) (eval_unary_poly d.inA)
    (eval_unary_poly d.inB) NUPPT.polyTimeComputable_inCoins
    (fun z => d.circuit (parameter z)) (fun z => d.seed (parameter z) (NUPPT.inCoins z))
    (fun z => d.input_range (parameter z))
    (fun z => d.key (parameter z) (NUPPT.inCoins z))

/-- The actual fake-message leaf is polynomial-time from the polynomial family, uniform
description generator, encryption algorithms, and seed block readers. No fake-message
computability assumption is required. [PS10, Theorem 163.7]

**Proof sketch.** Normalize the parameter before calling the unary uniform generator, so
every raw word receives the canonical description of the circuit at its parameter length.
The polynomial counts and bound are computed through the public unary polynomial routine.
Read the prescribed output from the argument's second component and the random tape from
its canonical field. Apply the complete fake garbling program to these selectors. Its input
range and output bounds follow from the family data; all key, nonce, and permutation premises
are exactly the supplied addressed seed readers. The public message equation identifies
the resulting actual encoded tables, active keys, and decoding pairs with this leaf. -/
theorem message_poly (d : Data) : PolyTimeComputable (message d) := by
  have hinA : ∀ z, d.inA.eval (parameter z) ≤ d.inputs.eval (parameter z) := by
    intro z
    have := d.input_range (parameter z)
    omega
  have hM := FakeProgram.message_poly d.E₁_poly d.E₂_poly
    parameter (fun z => d.bound.eval (parameter z)) (fun z => d.inputs.eval (parameter z))
    (fun z => d.inA.eval (parameter z)) (fun z => d.outLen.eval (parameter z))
    (description d) (fun z => pairSndD (NUPPT.inArg z)) NUPPT.inCoins
    parameter_unary_poly (eval_unary_poly d.bound) (eval_unary_poly d.inputs)
    (eval_unary_poly d.inA) (eval_unary_poly d.outLen) (description_poly d)
    (polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg)
    NUPPT.polyTimeComputable_inCoins (fun z => d.circuit (parameter z))
    (fun z => d.seed (parameter z) (NUPPT.inCoins z)) (fun z => d.output (parameter z))
    (description_shape d) hinA (fun z => d.output_lt (parameter z))
    (fun z => d.fanin (parameter z)) (fun z => d.key (parameter z) (NUPPT.inCoins z))
    (fun z => d.nonce₀ (parameter z) (NUPPT.inCoins z))
    (fun z => d.nonce₁ (parameter z) (NUPPT.inCoins z))
    (fun z => d.permutation (parameter z) (NUPPT.inCoins z))
  refine hM.congr fun z => ?_
  rw [message_eq, messageAt_eq, FakeObjects.message_eq]

/-- On every canonical layout, including arbitrary argument and tape lengths, the raw
message leaf is exactly the pointwise fake message at `n`, tape `r`, and output word `f`. -/
theorem message_layout (d : Data) (n : ℕ) (y f advice r : List Bool) :
    message d (NUPPT.layout (List.replicate n true) (pairEncode y f) advice r) =
      messageAt d n r f := by
  rw [message_eq, parameter_layout, NUPPT.inCoins_layout,
    NUPPT.inArg_layout, pairSndD_pairEncode]

/-- The complete encoded simulated-view map is polynomial-time from the actual derived
message and answer leaves. [PS10, Theorem 163.7] -/
theorem view_poly (d : Data) :
    PolyTimeComputable (BobSimulator.raw (message d) (answers d)) :=
  BobSimulator.raw_poly (message_poly d) (answers_poly d)

/-- The simulator is the existing Bob simulator specialized to the proved actual message
and answer leaves. Its data and coin polynomial are fixed before any distinguisher.
[PS10, Theorem 163.7] -/
noncomputable def simulator (d : Data) (coins : PolyExpr) : NUPPT :=
  BobSimulator.simulator (message_poly d) (answers_poly d) coins

/-- `simulator d coins = BobSimulator.simulator (message_poly d) (answers_poly d) coins`. -/
theorem simulator_eq (d : Data) (coins : PolyExpr) :
    simulator d coins = BobSimulator.simulator (message_poly d) (answers_poly d) coins := rfl

/-- The one fixed simulator is uniform for every supplied polynomial coin budget. -/
theorem simulator_uniform (d : Data) (coins : PolyExpr) : (simulator d coins).Uniform :=
  BobSimulator.simulator_uniform (message_poly d) (answers_poly d) coins

/-- The fixed simulator's coin polynomial is exactly the supplied `coins`. -/
theorem simulator_coins (d : Data) (coins : PolyExpr) : (simulator d coins).coins = coins :=
  BobSimulator.simulator_coins (message_poly d) (answers_poly d) coins

/-- On a canonical layout, the raw active-answer leaf is exactly the pointwise flat
answer at the parameter and raw simulator tape; it ignores argument and advice fields. -/
theorem answers_layout (d : Data) (n : ℕ) (arg advice r : List Bool) :
    answers d (NUPPT.layout (List.replicate n true) arg advice r) = answersAt d n r := by
  rw [answers_eq, parameter_layout, NUPPT.inCoins_layout]

/-- On any raw input/output/tape words, the one fixed simulator returns exactly Bob's
encoded view with the actual pointwise fake message and active answers, and an empty
private tape. This specializes the existing Bob simulator contract. [PS10, Theorem 163.7] -/
theorem simulator_runAtL (d : Data) (coins : PolyExpr) (n : ℕ) (y f r : List Bool) :
    (simulator d coins).runAtL n (pairEncode y f) r =
      (⟨List.replicate n true, pairEncode y (answersAt d n r),
        [], [messageAt d n r f]⟩ : View).encode := by
  rw [simulator_eq, BobSimulator.simulator_runAtL]
  simp only [message_layout, answers_layout]

/-- On a typed tape, the fixed simulator returns the same actual fake view with raw tape
`List.ofFn r`. The only randomness is its polynomial-budget tape. [PS10, Theorem 163.7] -/
theorem simulator_runAt (d : Data) (coins : PolyExpr) (n : ℕ) (y f : List Bool)
    (r : (simulator d coins).Coins n) :
    (simulator d coins).runAt n (pairEncode y f) r =
      (⟨List.replicate n true, pairEncode y (answersAt d n (List.ofFn r)),
        [], [messageAt d n (List.ofFn r) f]⟩ : View).encode := by
  rw [NUPPT.runAt_eq, simulator_runAtL]

/-- The ideal Bob sample is the actual fake view built from Bob's input, the prescribed
Bob output and the simulator tape, paired with Alice's true functionality output. The same
fixed simulator works before every input and distinguisher. [PS10, Theorem 163.7] -/
theorem idealB_eq (d : Data) (coins : PolyExpr) (F : Functionality) (n : ℕ)
    (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
    (r : (simulator d coins).Coins n) :
    F.idealB (simulator d coins) n x y r =
      pairEncode
        (⟨List.replicate n true, pairEncode (List.ofFn y) (answersAt d n (List.ofFn r)),
          [], [messageAt d n (List.ofFn r) (List.ofFn (F.f n x y).2)]⟩ : View).encode
        (List.ofFn (F.f n x y).1) := by
  simpa only [message_layout, answers_layout] using
    BobSimulator.idealB_eq (message_poly d) (answers_poly d) coins F n x y r

/-- On a typed prescribed output vector, `messageAt` uses its actual bits without padding:
`messageAt d n r (ofFn f) = FakeObjects.message ... f`. -/
theorem messageAt_ofFn (d : Data) (n : ℕ) (r : List Bool)
    (f : Fin (d.outLen.eval n) → Bool) :
    messageAt d n r (List.ofFn f) =
      FakeObjects.message (nestedSpecial d.E₁ d.E₂ n) (d.circuit n) (d.seed n r)
        (d.inA.eval n) (d.outLen.eval n) (d.output n) f := by
  rw [messageAt_eq]
  apply congrArg (FakeObjects.message (nestedSpecial d.E₁ d.E₂ n)
    (d.circuit n) (d.seed n r) (d.inA.eval n) (d.outLen.eval n) (d.output n))
  funext j
  rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; exact j.isLt), List.getElem_ofFn]

/-- For the public constructor, the actual fake-message word uses exactly the supplied
algorithms, circuit, seed, counts, output vertices and prescribed result bits.

**Proof sketch.** Read the stored constructor fields in the pointwise message equation;
all dependent circuit, output, and seed arguments are exposed together. -/
theorem Data.make_messageAt (n : ℕ) (r f : List Bool) :
    messageAt (Data.make
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation)) n r f =
      FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
        (inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false) := rfl

/-- For the public constructor, the active-answer word uses exactly the supplied circuit,
seed and polynomial input ranges.

**Proof sketch.** Read the constructor's circuit, seed and input-range fields in the
pointwise answer equation; both sides are the same finite vector. -/
theorem Data.make_answersAt (n : ℕ) (r : List Bool) :
    answersAt (Data.make
      (E₁ := E₁)
      (E₂ := E₂)
      (E₁_poly := E₁_poly)
      (E₂_poly := E₂_poly)
      (bound := bound)
      (inputs := inputs)
      (inA := inA)
      (inB := inB)
      (outLen := outLen)
      (gen := gen)
      (gen_poly := gen_poly)
      (circuit := circuit)
      (output := output)
      (shape := shape)
      (input_range := input_range)
      (output_lt := output_lt)
      (fanin := fanin)
      (seed := seed)
      (key := key)
      (nonce₀ := nonce₀)
      (nonce₁ := nonce₁)
      (permutation := permutation)) n r =
      List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n r)
        (inA.eval n) (inB.eval n)) := rfl

end Constructor

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator
