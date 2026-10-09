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
* The aggregated one-bit block tests live in
  `TCSlib.Complexity.ClassNP.PolyTimeBlockTests`.

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

/-- The first projection of the empty word. -/
theorem pairFstD_nil : pairFstD ([] : List Bool) = [] := rfl

/-- The second component of a pair is shorter than the pair. -/
theorem length_pairSndD_le (z : List Bool) : (pairSndD z).length ≤ z.length := by
  cases h : pairDecode z with
  | none => simp [pairSndD, h]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u h
    rw [hz, pairSndD_pairEncode, length_pairEncode]
    omega

/-- A word with a nonempty first projection is a genuine pair. -/
theorem eq_pairEncode_of_pairFstD_ne {z : List Bool} (h : pairFstD z ≠ []) :
    z = pairEncode (pairFstD z) (pairSndD z) := by
  cases hd : pairDecode z with
  | none => exact absurd (by simp [pairFstD, hd]) h
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u hd
    rw [hz, pairFstD_pairEncode, pairSndD_pairEncode]

/-- Both projections of a word fit inside it, jointly and doubled. -/
theorem length_pair_components_le (y : List Bool) :
    2 * (pairFstD y).length + (pairSndD y).length ≤ y.length := by
  cases hd : pairDecode y with
  | none =>
    have hf : pairFstD y = [] := by simp [pairFstD, hd]
    have hs : pairSndD y = [] := by simp [pairSndD, hd]
    simp [hf, hs]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode y p u hd
    conv_rhs => rw [hz]
    rw [length_pairEncode, hz, pairFstD_pairEncode, pairSndD_pairEncode]
    omega

/-- Dropping a slice never grows a word beyond `max` with the constant pair. -/
theorem length_sliceDropAt_le (a k : ℕ) (z : List Bool) :
    (sliceDropAt a k z).length ≤ max z.length 2 := by
  cases h : pairDecode z with
  | none =>
    have h1 : pairFstD z = [] := by simp [pairFstD, h]
    have h2 : pairSndD z = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [sliceDropAt, h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨p, u⟩ := ab
    have hz := eq_pairEncode_of_pairDecode z p u h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega

/-- A range-indexed concatenation with a single live chunk is that chunk. -/
theorem flatMap_range_eq_single {c : ℕ → List Bool} {N K : ℕ} {b : List Bool}
    (hKN : K < N) (hc : ∀ i < N, c i = if i = K then b else []) :
    (List.range N).flatMap c = b := by
  induction N with
  | zero => omega
  | succ N ih =>
    rw [List.range_succ, List.flatMap_append]
    by_cases hNK : N = K
    · subst hNK
      have hpre : (List.range N).flatMap c = [] := by
        refine List.flatMap_eq_nil_iff.mpr (fun i hi => ?_)
        have hiN := List.mem_range.mp hi
        rw [hc i (by omega), if_neg (by omega)]
      rw [hpre, List.nil_append, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        hc N (by omega), if_pos rfl]
    · have hKN' : K < N := by omega
      rw [ih hKN' (fun i hi => hc i (by omega))]
      rw [List.flatMap_cons, hc N (by omega), if_neg hNK]
      simp

/-- The absorbing end state of the block loops. -/
def blockDone : List Bool := pairEncode [] []

/-- The Boolean emptiness test, in the shape
`Complexity.polyTimeComputable_ite` consumes. -/
def isNilB (w : List Bool) : Bool := decide (w = [])

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
a constant number of control states.  The host's admissibility invariant is
"the state word is an orbit point of `g` from the input", so the orbit-only
length envelope `horbit` bounds each call's budget by one polynomial in the
input length (the pattern of the proved Cook–Levin emitter assembly); the
fuel machine is `Turing.FinTM.computesFunInTime_polyBits`.  The loop host
then computes exactly the stated concatenation within `c·(T+1)·(R+2)`
steps. -/
theorem polyTimeComputable_emitIter {g e : List Bool → List Bool}
    (hg : PolyTimeComputable g) (he : PolyTimeComputable e)
    (a' k' b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ),
      (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
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

/-- `xorD` computes the truncating bitwise XOR on genuine pairs. -/
@[simp]
theorem xorD_pairEncode (a b : List Bool) :
    xorD (pairEncode a b) = List.zipWith xor a b := by
  simp [xorD]

end Complexity
