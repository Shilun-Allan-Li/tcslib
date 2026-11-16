/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.ZeroKnowledge.Interaction
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Foundations.Experiments
import TCSlib.Cryptography.Foundations.Negligible

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Two-party secure computation in the honest-but-curious model (definitions)

[PS10, Definition 155.1]: a protocol `π` with security parameter `1^n` securely computes
`f(x, y)` in the honest-but-curious model if there are non-uniform PPT simulators `S_A`, `S_B`
such that, for all inputs `x, y`,
- `{S_A(x, f(x, y)), f(x, y)} ≈ {e ← [A(x) ↔ B(y)] : view_A(e), out_B(e)}`, and
- `{S_B(y, f(x, y)), f(x, y)} ≈ {e ← [A(x) ↔ B(y)] : view_B(e), out_A(e)}`.

The output clause makes the definition imply correctness: without it, a protocol in which both
parties output `0` would be secure (the source's remark).

**On the ch. 2–4 interaction model** (D8; ruling of 2026-11-05: strategies define). Alice plays
the prover's role and Bob the verifier's. The common input is `1^n`; Alice's input travels as the
prover's private input `y` of `Protocol` and Bob's as the verifier's auxiliary input `z`. The views
are `Protocol.viewP` and `Protocol.viewV`, the outputs `Protocol.outP` and `Protocol.outV`, and
a view reaches the distinguisher encoded (`View.encode`).

**Deviations.**
- **Private outputs.** The functionality has an output for each party, `f = (f_A, f_B)`. The
  definition writes one `f(x, y)` for both, but the oblivious-transfer functionality it is
  applied to (Def 160.a) has private outputs `(⊥, a_b)`.
- **Lengths.** Inputs and outputs have polynomial lengths in `n`, not exactly `n` (OT's inputs
  are bits).
- **Uniformity.** "For all `x, y`" is read with one negligible bound for all inputs of each
  length (`ε` before `x, y`), the convention of the ch. 2–4 layer's security definitions.
- **Polynomial time** (ruling of 2026-11-05). The definition leaves the parties' efficiency to
  §4.4's convention; here it is required (`Functionality.PolyTime`). Both strategies are PPT, and
  the messages of honest executions are polynomially bounded. Under D8, `Strategy.Efficient`
  alone bounds an activation by the length of the messages received, not by `n`.

## Main definitions

* `SecureComputation.Functionality`: a two-party functionality with private outputs.
* `Functionality.realA`, `idealA`, `realB`, `idealB`: the four samplers of Def 155.1.
* `SecureComputation.Functionality.PolyTime`: the parties run in polynomial time.
* `SecureComputation.HBCSecure`: [PS10, Definition 155.1].
* `SecureComputation.otFunctionality`: [PS10, Def 160.a], `OT(a₁, a₂, b) = (⊥, a_b)`.

## Main results

* `Functionality.realA_eq`, `realB_eq`, `idealA_eq`, `idealB_eq`: the four sampler equations.
* `Functionality.polyTime_iff`, `SecureComputation.hbcSecure_iff`: the time and security clauses.
* `SecureComputation.otFunctionality_inA`, `otFunctionality_inB`, `otFunctionality_outA`,
  `otFunctionality_outB`, `otFunctionality_f`: the OT functionality's fields.
* `SecureComputation.otFunctionality_f_snd`: the OT functionality gives Bob the chosen bit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and §6.2.4 (book pp. 155–156, 160).
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-- A **two-party functionality** with private outputs: Alice's and Bob's inputs have
`inA(n)` and `inB(n)` bits, and `f` gives Alice an `outA(n)`-bit and Bob an `outB(n)`-bit
output. -/
structure Functionality where
  /-- Alice's input length. -/
  inA : PolyExpr
  /-- Bob's input length. -/
  inB : PolyExpr
  /-- Alice's output length. -/
  outA : PolyExpr
  /-- Bob's output length. -/
  outB : PolyExpr
  /-- The function `(x, y) ↦ (f_A(x, y), f_B(x, y))`. -/
  f : ∀ n, (Fin (inA.eval n) → Bool) → (Fin (inB.eval n) → Bool) →
    (Fin (outA.eval n) → Bool) × (Fin (outB.eval n) → Bool)

namespace Functionality

variable (F : Functionality)

/-- **The real sampler for Alice's side**: on the coins of an honest execution
`A(x) ↔ B(y)` with common input `1^n`, the pair `⟨view_A, out_B⟩`. -/
def realA (π : Protocol) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    π.ExecCoins π.P (List.replicate n true) → List Bool := fun r =>
  pairEncode (π.viewP (List.replicate n true) (List.ofFn x) (List.ofFn y) r).encode
    (π.outV π.P (List.replicate n true) (List.ofFn x) (List.ofFn y) r)

/-- Alice's real sampler pairs her encoded view with Bob's output on the honest tapes. -/
theorem realA_eq (π : Protocol) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)) :
    F.realA π n x y r =
      pairEncode (π.viewP (List.replicate n true) (List.ofFn x) (List.ofFn y) r).encode
        (π.outV π.P (List.replicate n true) (List.ofFn x) (List.ofFn y) r) := rfl

/-- **The real sampler for Bob's side**: `⟨view_B, out_A⟩`. -/
def realB (π : Protocol) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    π.ExecCoins π.P (List.replicate n true) → List Bool := fun r =>
  pairEncode (π.viewV (List.replicate n true) (List.ofFn x) (List.ofFn y) r).encode
    (π.outP (List.replicate n true) (List.ofFn x) (List.ofFn y) r)

/-- Bob's real sampler pairs his encoded view with Alice's output on the honest tapes. -/
theorem realB_eq (π : Protocol) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)) :
    F.realB π n x y r =
      pairEncode (π.viewV (List.replicate n true) (List.ofFn x) (List.ofFn y) r).encode
        (π.outP (List.replicate n true) (List.ofFn x) (List.ofFn y) r) := rfl

/-- **The ideal sampler for Alice's side**: `⟨S_A(1^n, ⟨x, f_A(x, y)⟩), f_B(x, y)⟩`. -/
def idealA (S : NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    S.Coins n → List Bool := fun s =>
  pairEncode (S.runAt n (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) s)
    (List.ofFn (F.f n x y).2)

/-- Alice's ideal sampler pairs her simulation from her input and output with Bob's output. -/
theorem idealA_eq (S : NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (s : S.Coins n) :
    F.idealA S n x y s =
      pairEncode (S.runAt n (pairEncode (List.ofFn x) (List.ofFn (F.f n x y).1)) s)
        (List.ofFn (F.f n x y).2) := rfl

/-- **The ideal sampler for Bob's side**: `⟨S_B(1^n, ⟨y, f_B(x, y)⟩), f_A(x, y)⟩`. -/
def idealB (S : NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool) :
    S.Coins n → List Bool := fun s =>
  pairEncode (S.runAt n (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) s)
    (List.ofFn (F.f n x y).1)

/-- Bob's ideal sampler pairs his simulation from his input and output with Alice's output. -/
theorem idealB_eq (S : NUPPT) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (s : S.Coins n) :
    F.idealB S n x y s =
      pairEncode (S.runAt n (pairEncode (List.ofFn y) (List.ofFn (F.f n x y).2)) s)
        (List.ofFn (F.f n x y).1) := rfl

/-- **The parties run in polynomial time** on `F`'s inputs (ruling of 2026-11-05).
- Both strategies are PPT (`Strategy.Efficient`).
- For a polynomial `B`, in every honest execution with common input `1^n` and inputs of `F`'s
  lengths, every message has at most `B(n)` bits.

Under D8 a PPT strategy's activation is polynomial in its whole input, the messages received
included. With the honest messages bounded and `rounds(n)` activations, each party's work in an
honest execution (the only kind in this model) is polynomial in `n`. -/
def PolyTime (π : Protocol) : Prop :=
  π.P.Efficient ∧ π.V.Efficient ∧ ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)),
    ∀ msg ∈ (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
        (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
      msg.length ≤ B.eval n

/-- Polynomial time means efficient strategies and a uniform polynomial bound on every
message in every honest execution on inputs of the functionality's lengths. -/
theorem polyTime_iff (π : Protocol) :
    F.PolyTime π ↔
      π.P.Efficient ∧ π.V.Efficient ∧ ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool)
        (y : Fin (F.inB.eval n) → Bool) (r : π.ExecCoins π.P (List.replicate n true)),
        ∀ msg ∈ (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).1 ++
            (π.transcript (List.replicate n true) (List.ofFn x) (List.ofFn y) r).2,
          msg.length ≤ B.eval n := Iff.rfl

end Functionality

/-- **Honest-but-curious security** [PS10, Definition 155.1]: the parties run in polynomial time
(`Functionality.PolyTime`; see the module docstring), and there are non-uniform PPT simulators
`S_A`, `S_B` such that for every non-uniform PPT distinguisher `D` there is a negligible `ε` with,
for all `n` and all inputs `x`, `y`, `D`'s advantage between Alice's real and ideal samplers, and
between Bob's, at most `ε(n)`. -/
def HBCSecure (π : Protocol) (F : Functionality) : Prop :=
  F.PolyTime π ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
      distAdv (F.realA π n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
        distAdv (F.realB π n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n

/-- Honest-but-curious security consists of polynomial time and two simulators whose
distinguishing advantages have a negligible bound uniform over inputs of each length. -/
theorem hbcSecure_iff (π : Protocol) (F : Functionality) :
    HBCSecure π F ↔
      F.PolyTime π ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
          distAdv (F.realA π n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
            distAdv (F.realB π n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := Iff.rfl

/-- **1-out-of-2 oblivious transfer** [PS10, Def 160.a]: the sender Alice holds bits `(a₁, a₂)`,
the receiver Bob a choice bit `b` (`false` for `1`, `true` for `2`);
`OT(a₁, a₂, b) = (⊥, a_b)`, with Alice's `⊥` the empty output. -/
def otFunctionality : Functionality where
  inA := .const 2
  inB := .const 1
  outA := .const 0
  outB := .const 1
  f _ (a : Fin 2 → Bool) (b : Fin 1 → Bool) := (Fin.elim0, fun _ => a (if b 0 then 1 else 0))

/-- Alice's OT input consists of two bits. -/
theorem otFunctionality_inA : otFunctionality.inA = .const 2 := rfl

/-- Bob's OT input consists of one choice bit. -/
theorem otFunctionality_inB : otFunctionality.inB = .const 1 := rfl

/-- Alice's OT output is empty. -/
theorem otFunctionality_outA : otFunctionality.outA = .const 0 := rfl

/-- Bob's OT output consists of one bit. -/
theorem otFunctionality_outB : otFunctionality.outB = .const 1 := rfl

/-- OT returns the empty output to Alice and the selected input bit to Bob. -/
theorem otFunctionality_f (n : ℕ) (a : Fin 2 → Bool) (b : Fin 1 → Bool) :
    otFunctionality.f n a b =
      ((Fin.elim0 : Fin 0 → Bool), fun _ : Fin 1 => a (if b 0 then 1 else 0)) := rfl

/-- The OT functionality gives Bob the chosen bit. -/
theorem otFunctionality_f_snd (n : ℕ) (a : Fin 2 → Bool) (b : Fin 1 → Bool) :
    ((otFunctionality.f n a b).2 : Fin 1 → Bool) = fun _ => a (if b 0 then 1 else 0) := rfl

/-- Bob's OT output at any typed output index is Alice's input selected by Bob's typed choice
bit. The input indices use the published identifications of OT's two-bit and one-bit domains. -/
theorem otFunctionality_f_snd_apply (n : ℕ)
    (a : Fin (otFunctionality.inA.eval n) → Bool)
    (b : Fin (otFunctionality.inB.eval n) → Bool)
    (j : Fin (otFunctionality.outB.eval n)) :
    (otFunctionality.f n a b).2 j =
      a (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inA).trans
          (PolyExpr.eval_const 2 n)).symm
        (if b (Fin.cast ((congrArg (fun p : PolyExpr => p.eval n) otFunctionality_inB).trans
            (PolyExpr.eval_const 1 n)).symm (0 : Fin 1)) then (1 : Fin 2) else 0)) := rfl

end TCSlib.Cryptography.SecureComputation
