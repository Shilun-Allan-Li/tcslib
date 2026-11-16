/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeMessage
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeProgram
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.BobSimulator

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

## Main results

* The equation readers expose the exact canonical simulated message and answers.

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

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulator
