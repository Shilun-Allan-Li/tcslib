/-
Copyright (c) 2026 The TCSlib Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib Contributors
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.ClassNP.CounterProgPolyTime
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.ClassNP.PolyTimePrefix
import TCSlib.Complexity.TuringMachine.CounterProgInput
import TCSlib.Complexity.TuringMachine.Build.Loop
import TCSlib.Complexity.TuringMachine.Build.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bounded block-query loop

The chapter-neutral composition primitive behind "run a `P`-decider on
polynomially many fixed-size blocks of the input and aggregate the answers":
the folklore closure of polynomial time under polynomial repetition, used
tacitly throughout [AB09] (§7.3, proof of Theorem 7.8; §7.4.1, repeated
trials; proofs of Theorems 7.17 and 7.18).

Everything here lives at the level of `Complexity.PolyTimeComputable`; the
`P`-closure corollaries (`Complexity.mem_P_of_blockAny` and friends) are
stated in `TCSlib.Complexity.ClassNP.PClosure`, which imports this file.

## Main definitions

* `Complexity.blockAt` — the `i`-th length-`a·(n+1)^k` block of the second
  component of a pair, where `n` is the first component's length.
* `Complexity.sliceTakeAt` / `Complexity.sliceDropAt` — keep the first
  component and take/drop a polynomial-length prefix of the second.
* `Complexity.xorD` — truncating bitwise XOR of the two components of a pair.

## Main results

* `Complexity.polyTimeComputable_emitIter` — the machine-level loop: iterating
  a polynomial-time step function a polynomial number of times, concatenating
  a polynomial-time chunk of each iterate, is polynomial-time, provided the
  iterates stay inside a polynomial length envelope.  This is the one genuinely
  new combinator; it is built on `Turing.FinTM.exists_emitLoopTM` with
  clean-call modules (`Turing.FinTM.exists_installCallTM` /
  `exists_emitCallTM`) as the per-round body.
* `Complexity.polyTimeComputable_xorD` — truncating bitwise XOR is
  polynomial-time (a one-pass counter program).
* `Complexity.polyTimeComputable_blockAnyTest` /
  `_blockMajorityTest` / `_blockXorAnyTest` — the one-bit aggregated block
  tests (OR, strict majority, XOR-then-OR) of a polynomial-time one-bit
  indicator are polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3, Theorem 7.8; §7.4.1; Theorems
  7.17–7.18: the implicit "simulate the machine on each block" closures.)
-/

namespace Complexity

open Turing

/-! ### Slicing the second component at a polynomial schedule

The `Randomized`-layer `sliceTake`/`sliceDrop` of
`TCSlib.Complexity.Randomized.PolyTimeModel` are instances of the following
chapter-neutral forms (stated here, below the `Randomized` layer, so that the
block loop can be shared with the Chapter 3–4 development). -/

/-- Keep the first component of a pair and the first `a·(n+1)^k` symbols of its
second component, where `n` is the first component's length: on
`Turing.pairEncode x r` it returns `Turing.pairEncode x (r.take (a·(|x|+1)^k))`. -/
def sliceTakeAt (a k : ℕ) (z : List Bool) : List Bool :=
  pairEncode (pairFstD z) ((pairSndD z).take (a * ((pairFstD z).length + 1) ^ k))

/-- Keep the first component of a pair and drop the first `a·(n+1)^k` symbols of
its second component: on `Turing.pairEncode x r` it returns
`Turing.pairEncode x (r.drop (a·(|x|+1)^k))`. -/
def sliceDropAt (a k : ℕ) (z : List Bool) : List Bool :=
  pairEncode (pairFstD z) ((pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k))

/-- `sliceTakeAt a k` is polynomial-time computable.
**Proof sketch.** `a·(n+1)^k` is available as a unary string via
`Complexity.polyTimeComputable_polyUnary`; pair it with the second component and
apply the length-gated prefix primitive
`Complexity.polyTimeComputable_takePrefixByLength`, so no in-machine
exponentiation is needed. -/
theorem polyTimeComputable_sliceTakeAt (a k : ℕ) :
    PolyTimeComputable (sliceTakeAt a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (a * ((pairFstD z).length + 1) ^ k) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => pairEncode
      (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).take (a * ((pairFstD z).length + 1) ^ k)) := by
    have heq : (fun z => (pairSndD z).take (a * ((pairFstD z).length + 1) ^ k)) =
        PrefixByLength.take ∘ (fun z => pairEncode
          (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, PrefixByLength.take, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
    rw [heq]
    exact polyTimeComputable_takePrefixByLength.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-- `sliceDropAt a k` is polynomial-time computable.
**Proof sketch.** As `sliceTakeAt`, with
`Complexity.polyTimeComputable_dropPrefixByLength` in place of the take
primitive. -/
theorem polyTimeComputable_sliceDropAt (a k : ℕ) :
    PolyTimeComputable (sliceDropAt a k) := by
  have hu : PolyTimeComputable
      (fun z => List.replicate (a * ((pairFstD z).length + 1) ^ k) true) :=
    (polyTimeComputable_polyUnary a k).comp polyTimeComputable_pairFstD
  have henc : PolyTimeComputable (fun z => pairEncode
      (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) :=
    PolyTimeComputable.pairEncode hu polyTimeComputable_pairSndD
  have hg : PolyTimeComputable
      (fun z => (pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k)) := by
    have heq : (fun z => (pairSndD z).drop (a * ((pairFstD z).length + 1) ^ k)) =
        PrefixByLength.drop ∘ (fun z => pairEncode
          (List.replicate (a * ((pairFstD z).length + 1) ^ k) true) (pairSndD z)) := by
      funext z
      simp only [Function.comp, PrefixByLength.drop, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
    rw [heq]
    exact polyTimeComputable_dropPrefixByLength.comp henc
  exact PolyTimeComputable.pairEncode polyTimeComputable_pairFstD hg

/-! ### Small Boolean and list helpers -/

/-- Removing the head symbol is polynomial-time computable.
**Proof sketch.** `w.drop 1` is the length-gated drop
`Complexity.PrefixByLength.drop` applied to `Turing.pairEncode [true] w`. -/
theorem polyTimeComputable_tail : PolyTimeComputable (fun w => w.drop 1) := by
  have henc : PolyTimeComputable (fun w => pairEncode [true] w) :=
    (polyTimeComputable_const [true]).pairEncode polyTimeComputable_id
  have heq : (fun w : List Bool => w.drop 1) =
      PrefixByLength.drop ∘ (fun w => pairEncode [true] w) := by
    funext w
    simp [Function.comp, PrefixByLength.drop]
  rw [heq]
  exact polyTimeComputable_dropPrefixByLength.comp henc

/-- The emptiness test is polynomial-time computable (as a one-bit output).
**Proof sketch.** `w = []` iff `|w| ≤ |[]|`, the pair length test
`Complexity.polyTimeComputable_lenLe` at `Turing.pairEncode [] w`. -/
theorem polyTimeComputable_isNil :
    PolyTimeComputable (fun w => [decide (w = [])]) := by
  have henc : PolyTimeComputable (fun w => pairEncode [] w) :=
    (polyTimeComputable_const []).pairEncode polyTimeComputable_id
  have h := polyTimeComputable_lenLe.comp henc
  convert h using 1
  funext w
  simp only [Function.comp, pairFstD_pairEncode, pairSndD_pairEncode, List.length_nil,
    Nat.le_zero, List.length_eq_zero_iff]

/-- Polynomial-time Boolean disjunction of two one-bit tests. -/
theorem polyTimeComputable_or {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x || q x]) := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [true]) hq using 1
  funext x
  cases p x <;> rfl

/-- Polynomial-time Boolean negation of a one-bit test. -/
theorem polyTimeComputable_not {p : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x])) :
    PolyTimeComputable (fun x => [!p x]) := by
  convert polyTimeComputable_ite hp (polyTimeComputable_const [false])
    (polyTimeComputable_const [true]) using 1
  funext x
  cases p x <;> rfl

/-! ### The emit-iteration combinator -/

/-- **The bounded loop of polynomial-time rounds** — the machine-level engine
of every block-query closure: iterating a polynomial-time step function `g` a
polynomial number of times from the input, concatenating a polynomial-time
chunk `e` of each iterate, is again polynomial-time, provided every iterate
stays inside one polynomial length envelope `b·(n+1)^l` of the *original*
input length.

**Proof sketch.** An instance of `Turing.FinTM.exists_emitLoopTM`.  The body
machine copies its input onto work tape zero (the loop's round state) and
enters the anchor; each round is two clean calls on the tape-resident state
word — an emit-mode call (`Turing.FinTM.exists_emitCallTM`) forwarding the
chunk `e s` to the physical output, then an install-mode call
(`Turing.FinTM.exists_installCallTM`) replacing the word by `g s` — glued by
a constant number of control states.  The invariant `|s| ≤ b·(|w|+1)^l` is
preserved by hypothesis, so each call's budget is one polynomial in the input
length; the fuel machine is `Turing.FinTM.computesFunInTime_polyBits`.  The
loop host then computes exactly the stated concatenation within
`c·(T+1)·(R+2)` steps. -/
theorem polyTimeComputable_emitIter {g e : List Bool → List Bool}
    (hg : PolyTimeComputable g) (he : PolyTimeComputable e)
    (a' k' b l : ℕ)
    (hinit : ∀ n : ℕ, n ≤ b * (n + 1) ^ l)
    (hgrow : ∀ w s : List Bool, s.length ≤ b * (w.length + 1) ^ l →
      (g s).length ≤ b * (w.length + 1) ^ l) :
    PolyTimeComputable (fun w =>
      (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap (fun i => e (g^[i] w))) := by
  sorry

/-! ### Truncating bitwise XOR -/

/-- Bitwise XOR of the two components of a pair, truncating to the shorter
component (`List.zipWith` semantics); malformed pairs give `[]`. -/
def xorD (z : List Bool) : List Bool :=
  List.zipWith xor (pairFstD z) (pairSndD z)

/-- `xorD` is polynomial-time computable.
**Proof sketch.** A single left-to-right pass (`Complexity.CounterProg`):
parse the doubled first component while emitting nothing, keeping the last
parsed data bit in finite control — impossible, the first component is
unbounded; instead, a two-phase counter program interleaves: it re-reads the
input once per output symbol.  Concretely, for each index `j`, the `j`-th
output bit is `xor` of the `j`-th bits of the two components; a one-register
program emits it by scanning the doubled prefix with an offset counter.  The
abstract step count is quadratic in `|z|`, which
`Complexity.CounterProg.polyTimeComputable_of_goes` still compiles to a
polynomial bound.  (The truncating semantics on unequal lengths is the
audited ch7-phase1 finding 1 convention.) -/
theorem polyTimeComputable_xorD : PolyTimeComputable xorD := by
  sorry

/-! ### The aggregated block tests

`blockAt a k z i` is the `i`-th block of length `a·(n+1)^k` of the second
component of the pair `z`, where `n` is the first component's length.  The
three aggregated one-bit tests below are the `PolyTimeComputable` engines of
the `P`-closure lemmas `Complexity.mem_P_of_blockAny` /
`_blockMajority` / `_blockXorAny` in `TCSlib.Complexity.ClassNP.PClosure`. -/

/-- The `i`-th length-`a·(n+1)^k` block of the second component of a pair,
where `n` is the first component's length. -/
def blockAt (a k : ℕ) (z : List Bool) (i : ℕ) : List Bool :=
  ((pairSndD z).drop (i * (a * ((pairFstD z).length + 1) ^ k))).take
    (a * ((pairFstD z).length + 1) ^ k)

/-- The OR-aggregated block test of a polynomial-time one-bit indicator is
polynomial-time: one bit saying whether some of the `a'·(n+1)^k'` blocks of
length `a·(n+1)^k` passes the test on `Turing.pairEncode`d (first component,
block).

**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`.
The loop state is `pairEncode [flag] (pairEncode countdown (pairEncode x rem))`
with a unary countdown initialized at `a'·(|x|+1)^k'`
(`Complexity.polyTimeComputable_polyUnary`); each round ORs the indicator of
`sliceTakeAt a k` into the flag, drops the block (`sliceDropAt a k`), and
decrements; the chunk function emits `[flag]` exactly at countdown exhaustion
(the step then moves to an absorbing done state), so the concatenated output
is the single aggregated bit.  The orbit is computed in closed form by
induction on the round index. -/
theorem polyTimeComputable_blockAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [(List.range (a' * ((pairFstD z).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD z) (blockAt a k z i)))]) := by
  sorry

/-- The strict-majority-aggregated block test of a polynomial-time one-bit
indicator is polynomial-time.

**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
flag replaced by two unary vote counters (passed and failed blocks); at
countdown exhaustion the emitted bit is the strict comparison of their
lengths (`Complexity.polyTimeComputable_lenLe` after a `pairSwap`), which
equals `a'·(n+1)^k' < 2·(passed votes)` since the counts sum to the round
total. -/
theorem polyTimeComputable_blockMajorityTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun z =>
      [decide (a' * ((pairFstD z).length + 1) ^ k' <
        2 * (List.range (a' * ((pairFstD z).length + 1) ^ k')).countP
          (fun i => MultiTapeTM.indicator V
            (pairEncode (pairFstD z) (blockAt a k z i))))]) := by
  sorry

/-- The XOR-then-OR aggregated block test of a polynomial-time one-bit
indicator is polynomial-time: the input is a nested pair
`⟨⟨x, u⟩, v⟩`; block `i` is drawn from `u`, XORed bitwise with `v`
(truncating, `Complexity.xorD`), and tested paired with `x`.

**Proof sketch.** As `Complexity.polyTimeComputable_blockAnyTest`, with the
per-round test precomposed with the XOR mask: the loop state additionally
carries `v`, and the round's test input is
`pairEncode x (xorD (pairEncode v block))`
(`Complexity.polyTimeComputable_xorD`). -/
theorem polyTimeComputable_blockXorAnyTest {V : Language Bool}
    (hV : PolyTimeComputable (fun z => [MultiTapeTM.indicator V z]))
    (a k a' k' : ℕ) :
    PolyTimeComputable (fun w =>
      [(List.range (a' * ((pairFstD (pairFstD w)).length + 1) ^ k')).any
        (fun i => MultiTapeTM.indicator V (pairEncode (pairFstD (pairFstD w))
          (List.zipWith xor (pairSndD w) (blockAt a k (pairFstD w) i))))]) := by
  sorry

end Complexity
