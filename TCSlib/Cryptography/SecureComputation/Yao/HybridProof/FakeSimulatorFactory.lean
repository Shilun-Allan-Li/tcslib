/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Yao.HybridProof.FakeSimulator

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Fixed simulator contracts from supplied circuit and seed families

The factory consumes the existing data constructor once and returns simple word equations
on an abstract data value. This avoids downstream matching of its dependent constructor.

## Main definitions

None.

## Main results

* `exists_data`: supplied families admit data with the actual pointwise word equations.
* `exists_simulator`: one fixed uniform machine with actual run and ideal-sample equations.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, Theorem 163.7 (one fixed efficient simulator).
-/

namespace TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulatorFactory

open Complexity Turing BoolCircuit

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

include E₁_poly E₂_poly gen_poly shape input_range output_lt fanin key nonce₀ nonce₁ permutation

/-- The supplied algorithms, polynomial counts, circuit/output family and seed readers
admit one data value whose actual answer and message words are exactly those supplied.
The public data constructor and its word equations are consumed in a generic context.
[PS10, Theorem 163.7]
`∃ d : FakeSimulator.Data, (∀ n r, FakeSimulator.answersAt d n r = List.ofFn
(FakeObjects.activeAnswers (circuit n) (seed n r) (inA.eval n) (inB.eval n))) ∧ ∀ n r f,
FakeSimulator.messageAt d n r f = FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
(inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false)`.

**Proof sketch.** Construct the existing data value from the supplied fields. Apply each
of its pointwise constructor equations with every argument explicit. The resulting word
equations expose the dependent families together, without asking consumers to match them. -/
theorem exists_data :
    ∃ d : FakeSimulator.Data,
      (∀ n r, FakeSimulator.answersAt d n r =
        List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n r)
          (inA.eval n) (inB.eval n))) ∧
      ∀ n r f, FakeSimulator.messageAt d n r f =
        FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
          (inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false) := by
  refine ⟨FakeSimulator.Data.make
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
      (permutation := permutation), ?_, ?_⟩
  · intro n r
    exact FakeSimulator.Data.make_answersAt
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
      (permutation := permutation)
      n r
  · intro n r f
    exact FakeSimulator.Data.make_messageAt
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
      (permutation := permutation)
      n r f

/-- The supplied families admit one fixed uniform simulator with the prescribed coin
polynomial and exact raw-run and ideal-sampler equations in the original supplied families.
No downstream dependent-constructor matching or assumed leaf efficiency is needed.
[PS10, Theorem 163.7]
`∃ SB : NUPPT, SB.Uniform ∧ SB.coins = coins ∧ (∀ n y f r, SB.runAtL n (pairEncode y f) r =
(⟨List.replicate n true, pairEncode y (List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n r)
(inA.eval n) (inB.eval n))), [], [FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
(inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false)]⟩ : View).encode) ∧ ∀ (F :
Functionality) n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) (r : SB.Coins n),
F.idealB SB n x y r = pairEncode (⟨List.replicate n true, pairEncode (List.ofFn y) (List.ofFn
(FakeObjects.activeAnswers (circuit n) (seed n (List.ofFn r)) (inA.eval n) (inB.eval n))), [],
[FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n (List.ofFn r)) (inA.eval n)
(outLen.eval n) (output n) (fun j => (List.ofFn (F.f n x y).2).getD j false)]⟩ : View).encode
(List.ofFn (F.f n x y).1)`.

**Proof sketch.** Obtain the existing data value together with its two plain word equations.
Choose the previously proved uniform simulator on this data. Its coin contract supplies the
budget. Specialize its raw-run and ideal-sampler contracts, then replace the pointwise answer
and message words using the two supplied equations. This keeps the machine fixed before
any input, functionality, or distinguisher is introduced. -/
theorem exists_simulator (coins : PolyExpr) :
    ∃ SB : NUPPT, SB.Uniform ∧ SB.coins = coins ∧
      (∀ n y f r, SB.runAtL n (pairEncode y f) r =
        (⟨List.replicate n true, pairEncode y
          (List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n r)
            (inA.eval n) (inB.eval n))), [],
          [FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n r)
            (inA.eval n) (outLen.eval n) (output n) (fun j => f.getD j false)]⟩ : View).encode) ∧
      ∀ (F : Functionality) n (x : Fin (F.inA.eval n) → Bool)
        (y : Fin (F.inB.eval n) → Bool) (r : SB.Coins n),
        F.idealB SB n x y r =
          pairEncode
            (⟨List.replicate n true, pairEncode (List.ofFn y)
              (List.ofFn (FakeObjects.activeAnswers (circuit n) (seed n (List.ofFn r))
                (inA.eval n) (inB.eval n))), [],
              [FakeObjects.message (nestedSpecial E₁ E₂ n) (circuit n) (seed n (List.ofFn r))
                (inA.eval n) (outLen.eval n) (output n)
                (fun j => (List.ofFn (F.f n x y).2).getD j false)]⟩ : View).encode
            (List.ofFn (F.f n x y).1) := by
  obtain ⟨d, ha, hm⟩ := exists_data
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
      (permutation := permutation)
  refine ⟨FakeSimulator.simulator d coins, FakeSimulator.simulator_uniform d coins,
    FakeSimulator.simulator_coins d coins, ?_, ?_⟩
  · intro n y f r
    rw [FakeSimulator.simulator_runAtL, ha, hm]
  · intro F n x y r
    rw [FakeSimulator.idealB_eq, ha, hm]

end TCSlib.Cryptography.SecureComputation.YaoHybridProof.FakeSimulatorFactory
