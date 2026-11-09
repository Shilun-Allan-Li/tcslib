/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Defs

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Honest-but-curious protocols in a hybrid model, ideal calls first (statement phase)

The `G`-hybrid model of [Gol04, §7.3.1] (oracle-aided protocols): the parties may hand inputs to
a trusted party computing a functionality `G` and receive its outputs. A protocol secure in that
model, with `G` then realized by a secure protocol, gives a secure protocol. This is
[Gol04, Theorem 7.3.3], the composition theorem (`SecureComputation/Compose.lean`).

[PS10]'s proof of Theorem 163.7 uses this step without stating it (inventory Thm-163.7). By the
ruling of 2026-11-05, Yao's protocol is first stated and proved in the OT-hybrid model, and the
real protocol follows by composition.

**The special case taken: all ideal calls first.** A `HybridProtocol G` makes `calls(n)` ideal
calls to `G`, then runs a protocol `main` of the ch. 2–4 model (D8).
- Each party computes its input to every call from `1^n`, its own input and its own coins (its
  coins in `main`), before any message. Yao's protocol is of this form: Alice's inputs are her
  wire keys (from her coins), Bob's are his input bits.
- In `main`, each party's private input is its input paired with its answers from the calls.
  Its view in `main` therefore holds its input, its coins, its answers and the messages it
  received: the view of [Gol04]'s oracle-aided protocol.
- Gol04's general form, with calls interleaved with messages, is not needed for Yao, and is not
  formalized.

**Security** is Definition 155.1 with the hybrid execution in the real samplers
(`HybridProtocol.HBCSecure`). It includes polynomial time (ruling of 2026-11-05):
- `main`'s strategies are PPT;
- the call inputs are polynomial-time computable;
- the messages of hybrid executions are polynomially bounded.

## Main definitions

* `SecureComputation.HybridProtocol`: a protocol in the `G`-hybrid model, ideal calls first.
* `HybridProtocol.answersA`, `answersB`, `privA`, `privB`: the answers and the private inputs
  of `main`.
* `HybridProtocol.realA`, `realB`: the real samplers of Definition 155.1 in the hybrid model.
* `HybridProtocol.PolyTime`, `HybridProtocol.HBCSecure`: polynomial time and security in the
  hybrid model.

## Main results

* `HybridProtocol.answersA_eq`, `answersB_eq`, `privA_eq`, `privB_eq`, `coins_eq`: the answers,
  complete private-input words and coin type.
* `HybridProtocol.realA_eq`, `realB_eq`, `polyTime_iff`, `hbcSecure_iff`: the sampler, time and
  security clauses.
* `HybridProtocol.pairFstD_privA`, `pairSndD_privA`, `pairFstD_privB`, `pairSndD_privB`: a
  party's private input in `main` decodes to its input and its answers.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §6.2, Definition 155.1 and Theorem 163.7 (book pp. 155–164).
* [Gol04] O. Goldreich, *Foundations of Cryptography, Volume 2*, Cambridge University Press,
  2004, §7.3.1 (oracle-aided protocols, privacy reductions) and Theorem 7.3.3.
-/

namespace TCSlib.Cryptography.SecureComputation

open Complexity Turing TCSlib.Cryptography

/-- **A protocol in the `G`-hybrid model, ideal calls first** [Gol04, §7.3.1, oracle-aided
protocols, specialized]: `calls(n)` calls to a trusted party computing `G`, whose inputs each
party computes from `1^n`, its input and its coins in `main`; then the protocol `main`, in which
each party's private input is its input paired with its answers. -/
structure HybridProtocol (G : Functionality) where
  /-- The protocol run after the ideal calls. -/
  main : Protocol
  /-- The number of ideal calls. -/
  calls : PolyExpr
  /-- Alice's input to call `j`, from `n`, her input and her coins. -/
  callA : ∀ n, List Bool → List Bool → Fin (calls.eval n) → Fin (G.inA.eval n) → Bool
  /-- Bob's input to call `j`, from `n`, his input and his coins. -/
  callB : ∀ n, List Bool → List Bool → Fin (calls.eval n) → Fin (G.inB.eval n) → Bool

namespace HybridProtocol

variable {G : Functionality} (H : HybridProtocol G)

/-- **Alice's answers**: her outputs from the `calls(n)` ideal calls, concatenated, for the
inputs `x`, `y` and the coins `rA`, `rB`. -/
def answersA (n : ℕ) (x y rA rB : List Bool) : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval n) =>
    List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).1).flatten

/-- Alice's answers are the concatenation of her ideal outputs in call order. -/
theorem answersA_eq (n : ℕ) (x y rA rB : List Bool) :
    H.answersA n x y rA rB =
      (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).1).flatten := rfl

/-- **Bob's answers**: his outputs from the ideal calls, concatenated. -/
def answersB (n : ℕ) (x y rA rB : List Bool) : List Bool :=
  (List.ofFn fun j : Fin (H.calls.eval n) =>
    List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).2).flatten

/-- Bob's answers are the concatenation of his ideal outputs in call order. -/
theorem answersB_eq (n : ℕ) (x y rA rB : List Bool) :
    H.answersB n x y rA rB =
      (List.ofFn fun j : Fin (H.calls.eval n) =>
        List.ofFn (G.f n (H.callA n x rA j) (H.callB n y rB j)).2).flatten := rfl

/-- Alice's private input in `main`: `⟨x, her answers⟩`. -/
def privA (n : ℕ) (x y rA rB : List Bool) : List Bool := pairEncode x (H.answersA n x y rA rB)

/-- Alice's complete private-input word pairs her original input with her ideal answers. -/
theorem privA_eq (n : ℕ) (x y rA rB : List Bool) :
    H.privA n x y rA rB = pairEncode x (H.answersA n x y rA rB) := rfl

/-- Bob's private input in `main`: `⟨y, his answers⟩`. -/
def privB (n : ℕ) (x y rA rB : List Bool) : List Bool := pairEncode y (H.answersB n x y rA rB)

/-- Bob's complete private-input word pairs his original input with his ideal answers. -/
theorem privB_eq (n : ℕ) (x y rA rB : List Bool) :
    H.privB n x y rA rB = pairEncode y (H.answersB n x y rA rB) := rfl

/-- Alice's private input decodes to her input. -/
@[simp] theorem pairFstD_privA (n : ℕ) (x y rA rB : List Bool) :
    pairFstD (H.privA n x y rA rB) = x := by
  simp [privA]

/-- Alice's private input decodes to her answers. -/
@[simp] theorem pairSndD_privA (n : ℕ) (x y rA rB : List Bool) :
    pairSndD (H.privA n x y rA rB) = H.answersA n x y rA rB := by
  simp [privA]

/-- Bob's private input decodes to his input. -/
@[simp] theorem pairFstD_privB (n : ℕ) (x y rA rB : List Bool) :
    pairFstD (H.privB n x y rA rB) = y := by
  simp [privB]

/-- Bob's private input decodes to his answers. -/
@[simp] theorem pairSndD_privB (n : ℕ) (x y rA rB : List Bool) :
    pairSndD (H.privB n x y rA rB) = H.answersB n x y rA rB := by
  simp [privB]

/-- The coins of a hybrid execution at `n`: Alice's and Bob's tapes in `main`. -/
abbrev Coins (n : ℕ) : Type := H.main.ExecCoins H.main.P (List.replicate n true)

/-- The hybrid coin type is the pair of main-protocol tapes on the unary common input. -/
theorem coins_eq (n : ℕ) :
    H.Coins n = H.main.ExecCoins H.main.P (List.replicate n true) := rfl

/-- **The hybrid real sampler for Alice's side**: on the coins of a hybrid execution with common
input `1^n`, `⟨view_A, out_B⟩`, where Alice's view in `main` holds her input, her answers, her
coins and the messages she received. -/
def realA (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) : H.Coins n → List Bool := fun r =>
  pairEncode (H.main.viewP (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
    (H.main.outV H.main.P (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r)

/-- Alice's hybrid real sampler pairs her main-protocol view with Bob's output, using the
complete private inputs formed from the parties' inputs and ideal answers. -/
theorem realA_eq (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n) :
    H.realA F n x y r =
      pairEncode (H.main.viewP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
        (H.main.outV H.main.P (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r) := rfl

/-- **The hybrid real sampler for Bob's side**: `⟨view_B, out_A⟩`. -/
def realB (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) : H.Coins n → List Bool := fun r =>
  pairEncode (H.main.viewV (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
    (H.main.outP (List.replicate n true)
      (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
      (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r)

/-- Bob's hybrid real sampler pairs his main-protocol view with Alice's output, using the
complete private inputs formed from the parties' inputs and ideal answers. -/
theorem realB_eq (F : Functionality) (n : ℕ) (x : Fin (F.inA.eval n) → Bool)
    (y : Fin (F.inB.eval n) → Bool) (r : H.Coins n) :
    H.realB F n x y r =
      pairEncode (H.main.viewV (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r).encode
        (H.main.outP (List.replicate n true)
          (H.privA n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2))
          (H.privB n (List.ofFn x) (List.ofFn y) (List.ofFn r.1) (List.ofFn r.2)) r) := rfl

/-- **The parties run in polynomial time** in the hybrid model, on `F`'s inputs (ruling of
2026-11-05, as `Functionality.PolyTime`):
- `main`'s strategies are PPT;
- the call inputs are computed in polynomial time from `⟨1^n, ⟨input, ⟨coins, 1^j⟩⟩⟩`;
- for a polynomial `B`, every message of `main` has at most `B(n)` bits, in every execution on
  private inputs of the hybrid format `⟨input, answers⟩`, for **any** answers of the right
  lengths. The ideal answers are a special case. The composition theorem feeds `main` the
  sub-protocol's outputs, which equal the ideal answers only computationally. -/
def PolyTime (F : Functionality) : Prop :=
  H.main.P.Efficient ∧ H.main.V.Efficient ∧
    (∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
        f (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
          (List.replicate j true)))) = List.ofFn (H.callA n x r j)) ∧
    (∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
        f (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
          (List.replicate j true)))) = List.ofFn (H.callB n y r j)) ∧
    ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
      (aA : Fin (H.calls.eval n * G.outA.eval n) → Bool)
      (aB : Fin (H.calls.eval n * G.outB.eval n) → Bool) (r : H.Coins n),
      ∀ msg ∈ (H.main.transcript (List.replicate n true)
          (pairEncode (List.ofFn x) (List.ofFn aA))
          (pairEncode (List.ofFn y) (List.ofFn aB)) r).1 ++
        (H.main.transcript (List.replicate n true)
          (pairEncode (List.ofFn x) (List.ofFn aA))
          (pairEncode (List.ofFn y) (List.ofFn aB)) r).2,
        msg.length ≤ B.eval n

/-- Hybrid polynomial time consists of efficient main strategies, polynomial-time call inputs,
and a polynomial bound on messages for every pair of answer strings of the required lengths.

**Proof sketch.** The right-hand side repeats the definition's strategy, call-input and
message-bound clauses in the same order, so the equivalence is reflexive. -/
theorem polyTime_iff (F : Functionality) :
    H.PolyTime F ↔
      H.main.P.Efficient ∧ H.main.V.Efficient ∧
        (∃ f : List Bool → List Bool, PolyTimeComputable f ∧
          ∀ n (x r : List Bool) (j : Fin (H.calls.eval n)),
            f (pairEncode (List.replicate n true) (pairEncode x (pairEncode r
              (List.replicate j true)))) = List.ofFn (H.callA n x r j)) ∧
        (∃ f : List Bool → List Bool, PolyTimeComputable f ∧
          ∀ n (y r : List Bool) (j : Fin (H.calls.eval n)),
            f (pairEncode (List.replicate n true) (pairEncode y (pairEncode r
              (List.replicate j true)))) = List.ofFn (H.callB n y r j)) ∧
        ∃ B : PolyExpr, ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool)
          (aA : Fin (H.calls.eval n * G.outA.eval n) → Bool)
          (aB : Fin (H.calls.eval n * G.outB.eval n) → Bool) (r : H.Coins n),
          ∀ msg ∈ (H.main.transcript (List.replicate n true)
              (pairEncode (List.ofFn x) (List.ofFn aA))
              (pairEncode (List.ofFn y) (List.ofFn aB)) r).1 ++
            (H.main.transcript (List.replicate n true)
              (pairEncode (List.ofFn x) (List.ofFn aA))
              (pairEncode (List.ofFn y) (List.ofFn aB)) r).2,
            msg.length ≤ B.eval n := Iff.rfl

/-- **Honest-but-curious security in the `G`-hybrid model** [PS10, Definition 155.1, with the
hybrid execution of [Gol04, §7.3.1]]: the parties run in polynomial time (`PolyTime`), and
there are non-uniform PPT simulators `S_A`, `S_B` such that for every non-uniform PPT
distinguisher `D` there is a negligible `ε` with, for all `n` and all inputs `x`, `y`, `D`'s
advantage between Alice's hybrid real and ideal samplers, and between Bob's, at most `ε(n)`. -/
def HBCSecure (F : Functionality) : Prop :=
  H.PolyTime F ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
      distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
        distAdv (H.realB F n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n

/-- Hybrid honest-but-curious security consists of hybrid polynomial time and two simulators
with negligible distinguishing advantages uniform over inputs of each length. -/
theorem hbcSecure_iff (F : Functionality) :
    H.HBCSecure F ↔
      H.PolyTime F ∧ ∃ SA SB : NUPPT, ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧
        ∀ n (x : Fin (F.inA.eval n) → Bool) (y : Fin (F.inB.eval n) → Bool),
          distAdv (H.realA F n x y) (F.idealA SA n x y) (D.distinguisherL n) ≤ ε n ∧
            distAdv (H.realB F n x y) (F.idealB SB n x y) (D.distinguisherL n) ≤ ε n := Iff.rfl

end HybridProtocol

end TCSlib.Cryptography.SecureComputation
