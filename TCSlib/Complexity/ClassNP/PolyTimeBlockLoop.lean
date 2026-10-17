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
import TCSlib.Complexity.TuringMachine.Build.EmitIterBody

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The bounded block-query loop

The chapter-neutral composition primitive behind "run a `P`-decider on
polynomially many fixed-size blocks of the input and aggregate the answers":
the folklore closure of polynomial time under polynomial repetition, used
tacitly throughout [AB09] (§7.3, proof of Theorem 7.8; §7.4.1, repeated
trials; proofs of Theorems 7.14 and 7.15).

Everything here lives at the level of `Complexity.PolyTimeComputable`; the
`P`-closure corollaries (`Complexity.mem_P_of_blockAny` and friends) are
stated in `TCSlib.Complexity.ClassNP.PClosure`, which imports this file.

## Main definitions

* `Complexity.sliceTakeAt` / `Complexity.sliceDropAt` — keep the first
  component and take/drop a polynomial-length prefix of the second.
* `Complexity.xorD` — truncating bitwise XOR of the two components of a pair.
* `Complexity.BlockLoop.step` / `Complexity.BlockLoop.emit` — one round and the chunk
  function of a countdown block loop.

## Main results

* `Complexity.polyTimeComputable_emitIter` — the machine-level loop: iterating
  a polynomial-time step function a polynomial number of times, concatenating
  a polynomial-time chunk of each iterate, is polynomial-time, provided the
  iterates stay inside a polynomial length envelope.  This is the one genuinely
  new combinator; it is built on `Turing.FinTM.exists_emitLoopTM` with
  clean-call modules (`Turing.FinTM.exists_installCallTM` /
  `exists_emitCallTM`) as the per-round body.
* `Complexity.polyTimeComputable_xorD` — truncating bitwise XOR is
  polynomial-time, via the emit-iteration loop.
* `Complexity.BlockLoop` — the countdown block loop shared by the aggregated block
  tests: the round `BlockLoop.step` and chunk `BlockLoop.emit`, their polynomial-time,
  length and orbit facts, and the assembled engines
  `BlockLoop.polyTimeComputable_countdown` and `BlockLoop.polyTimeComputable_of_loop`.
* The aggregated one-bit block tests live in
  `TCSlib.Complexity.ClassNP.PolyTimeBlockTests`.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§7.3, Theorem 7.8; §7.4.1; Theorems
  7.14–7.15: the implicit "simulate the machine on each block" closures.)
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

/-- **Dropping leading letters of the components keeps a pair state within `max |s| 2`**:
re-pairing the two components of `s` with `i` and `j` leading letters dropped gives a word no
longer than `s`, or than the empty pair (length `2`) when `s` is not a pair. It is the length
bound of the pair-stepping block loops (`xorPairStep` here, the level-bit loop of the `TQBF`
reduction).

**Proof sketch.** If `s` decodes as `⟨a, b⟩`, the new pair is no longer than `s`
(`length_pairEncode`); otherwise both components are empty and the new pair is the empty
pair. -/
theorem length_pairEncode_drop_le (s : List Bool) (i j : ℕ) :
    (pairEncode ((pairFstD s).drop i) ((pairSndD s).drop j)).length ≤ max s.length 2 := by
  cases h : pairDecode s with
  | none =>
    have h1 : pairFstD s = [] := by simp [pairFstD, h]
    have h2 : pairSndD s = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode s a b h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode, List.length_drop]
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

/-- Keeping only the head symbol is polynomial-time computable.
**Proof sketch.** `w.take 1` is the length-gated take
`Complexity.PrefixByLength.take` applied to `Turing.pairEncode [true] w`. -/
theorem polyTimeComputable_take1 : PolyTimeComputable (fun w => w.take 1) := by
  have henc : PolyTimeComputable (fun w => pairEncode [true] w) :=
    (polyTimeComputable_const [true]).pairEncode polyTimeComputable_id
  have heq : (fun w : List Bool => w.take 1) =
      PrefixByLength.take ∘ (fun w => pairEncode [true] w) := by
    funext w
    simp [Function.comp, PrefixByLength.take]
  rw [heq]
  exact polyTimeComputable_takePrefixByLength.comp henc

/-- The head bit (defaulting to `false`) is polynomial-time computable as a
one-bit output.
**Proof sketch.** `[w.headD false] = (w ++ [false]).take 1`. -/
theorem polyTimeComputable_headD :
    PolyTimeComputable (fun w => [w.headD false]) := by
  have happ : PolyTimeComputable (fun w : List Bool => w ++ [false]) :=
    PolyTimeComputable.append polyTimeComputable_id (polyTimeComputable_const [false])
  have heq : (fun w : List Bool => [w.headD false]) =
      (fun w : List Bool => w.take 1) ∘ (fun w : List Bool => w ++ [false]) := by
    funext w
    cases w <;> simp [Function.comp]
  rw [heq]
  exact polyTimeComputable_take1.comp happ

/-! ### The emit-iteration combinator -/

/-- **The bounded loop of polynomial-time rounds** — the machine-level engine
of every block-query closure: iterating a polynomial-time step function `g` a
polynomial number of times from the input, concatenating a polynomial-time
chunk `e` of each iterate, is again polynomial-time, provided every iterate
stays inside one polynomial length envelope `b·(n+1)^l` of the *original*
input length.

**Proof sketch.** Unpack the two machines and apply
`Turing.FinTM.exists_emitIterTM` (in
`TCSlib.Complexity.TuringMachine.Build.EmitIterBody`): an instance of
`Turing.FinTM.exists_emitLoopTM` whose body copies its input onto work tape
zero and runs each round as two clean calls on the tape-resident state word —
an emit-mode call (`Turing.FinTM.exists_emitCallTM`) forwarding the chunk
`e s`, then an install-mode call (`Turing.FinTM.exists_installCallTM`)
replacing the word by `g s`.  The host's admissibility invariant is "the
state word is an orbit point of `g` from the input", so the orbit-only
length envelope `horbit` bounds each call's budget by one polynomial in the
input length; the fuel machine is
`Turing.FinTM.computesFunInTime_polyBits`. -/
theorem polyTimeComputable_emitIter {g e : List Bool → List Bool}
    (hg : PolyTimeComputable g) (he : PolyTimeComputable e)
    (a' k' b l : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ),
      (g^[i] w).length ≤ b * (w.length + 1) ^ l) :
    PolyTimeComputable (fun w =>
      (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap (fun i => e (g^[i] w))) := by
  obtain ⟨G, CG, cG, hG⟩ := hg
  obtain ⟨E, CE, cE, hE⟩ := he
  obtain ⟨M, C, c, hM⟩ :=
    FinTM.exists_emitIterTM G E g e CG cG CE cE hG hE a' k' b l horbit
  exact ⟨M, C, c, hM⟩

/-! ### The countdown block loop

The OR, XOR-then-OR and strict-majority block tests (`PolyTimeBlockTests`,
`PolyTimeBlockMajority`) run one loop shape on the state word
`pairEncode h (pairEncode cd r)`: a head `h` (flag or live marker), a unary countdown
`cd`, and a remainder `r` carrying the scanned pair and any accumulated data.  The
declarations below prove that shape's polynomial-time, length, orbit and emission facts
once, for arbitrary head and remainder updates; each block test supplies only its own
update, per-round test and output. -/

namespace BlockLoop

/-- One round of a countdown block loop: on `pairEncode h (pairEncode cd r)` with `h` and
`cd` nonempty it returns `pairEncode (upd h r) (pairEncode (cd.drop 1) (nxt h r))`; a state
whose head (done or malformed) or countdown is empty goes to the absorbing `blockDone`. -/
def step (upd nxt : List Bool → List Bool → List Bool) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then blockDone
  else if isNilB (pairFstD (pairSndD s)) then blockDone
  else
    pairEncode (upd (pairFstD s) (pairSndD (pairSndD s)))
      (pairEncode ((pairFstD (pairSndD s)).drop 1) (nxt (pairFstD s) (pairSndD (pairSndD s))))

/-- The chunk function of a countdown block loop: `out s` exactly when the head of `s` is
nonempty and its countdown is empty, and `[]` otherwise. -/
def emit (out : List Bool → List Bool) (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) then []
  else if isNilB (pairFstD (pairSndD s)) then out s
  else []

/-- The head guard of a countdown block loop is polynomial-time. -/
private theorem polyTimeComputable_headNil :
    PolyTimeComputable (fun s => [isNilB (pairFstD s)]) :=
  polyTimeComputable_isNil.comp polyTimeComputable_pairFstD

/-- The countdown guard of a countdown block loop is polynomial-time. -/
private theorem polyTimeComputable_countdownNil :
    PolyTimeComputable (fun s => [isNilB (pairFstD (pairSndD s))]) :=
  polyTimeComputable_headNil.comp polyTimeComputable_pairSndD

/-- A countdown block loop's round `g = step upd nxt` is polynomial-time whenever its head
and remainder updates, read off the state, are (one `ite` on the disjunction of the two emptiness guards). -/
theorem polyTimeComputable_step {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt)
    (hu : PolyTimeComputable (fun s => upd (pairFstD s) (pairSndD (pairSndD s))))
    (hn : PolyTimeComputable (fun s => nxt (pairFstD s) (pairSndD (pairSndD s)))) :
    PolyTimeComputable g := by
  subst hg
  have hcd : PolyTimeComputable (fun s => pairFstD (pairSndD s)) :=
    polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hdone := polyTimeComputable_or polyTimeComputable_headNil polyTimeComputable_countdownNil
  convert polyTimeComputable_ite hdone (polyTimeComputable_const blockDone)
    (hu.pairEncode ((polyTimeComputable_tail.comp hcd).pairEncode hn)) using 1
  funext s
  unfold step isNilB
  cases decide (pairFstD s = []) <;> cases decide (pairFstD (pairSndD s) = []) <;> rfl

/-- The chunk function `emit out` is polynomial-time whenever `out` is. -/
theorem polyTimeComputable_emit {out : List Bool → List Bool}
    (ho : PolyTimeComputable out) : PolyTimeComputable (emit out) := by
  have hnone : PolyTimeComputable (fun _ : List Bool => ([] : List Bool)) :=
    polyTimeComputable_const []
  exact polyTimeComputable_ite polyTimeComputable_headNil hnone
    (polyTimeComputable_ite polyTimeComputable_countdownNil ho hnone)

/-- The initial state `pairEncode h₀ (pairEncode cd (r z))`, with unary countdown `cd` of
length `a'·(|x z|+1)^k'`, is polynomial-time whenever `x` and `r` are. -/
theorem polyTimeComputable_countdownInit (h₀ : List Bool) {x r : List Bool → List Bool}
    (hx : PolyTimeComputable x) (hr : PolyTimeComputable r) (a' k' : ℕ) :
    PolyTimeComputable (fun z => pairEncode h₀
      (pairEncode (List.replicate (a' * ((x z).length + 1) ^ k') true) (r z))) :=
  (polyTimeComputable_const h₀).pairEncode
    (((polyTimeComputable_polyUnary a' k').comp hx).pairEncode hr)

/-- `blockDone` is absorbing for every countdown block loop. -/
theorem step_done {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt) :
    g blockDone = blockDone := by
  subst hg
  simp [step, blockDone, isNilB]

/-- One round of a countdown block loop respects the slack measure `|s| + c·|cd s|`
(`cd s = pairFstD (pairSndD s)`), up to `max _ 2`, provided every live update satisfies
`2·|upd h r| + |nxt h r| ≤ 2·|h| + |r| + 2 + c`.
**Proof sketch.** The done branches give `blockDone`; a live round on `⟨h, ⟨cd, r⟩⟩` drops
one countdown symbol, two symbols of encoding and `c` of slack, paying for the growth. -/
theorem length_step_le {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt) (c : ℕ)
    (hlive : ∀ h r, h ≠ [] →
      2 * (upd h r).length + (nxt h r).length ≤ 2 * h.length + r.length + 2 + c)
    (s : List Bool) :
    (g s).length + c * (pairFstD (pairSndD (g s))).length ≤
      max (s.length + c * (pairFstD (pairSndD s)).length) 2 := by
  subst hg
  unfold step
  cases h1 : isNilB (pairFstD s) with
  | true =>
    simp only [↓reduceIte]
    refine le_trans ?_ (le_max_right _ _)
    simp [blockDone, length_pairEncode, pairFstD_nil]
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte]
    cases h2 : isNilB (pairFstD (pairSndD s)) with
    | true =>
      simp only [↓reduceIte]
      refine le_trans ?_ (le_max_right _ _)
      simp [blockDone, length_pairEncode, pairFstD_nil]
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      have hf : pairFstD s ≠ [] := by simpa [isNilB] using h1
      have hcd : pairFstD (pairSndD s) ≠ [] := by simpa [isNilB] using h2
      have hs := eq_pairEncode_of_pairFstD_ne hf
      have ht := eq_pairEncode_of_pairFstD_ne hcd
      refine le_trans ?_ (le_max_left _ _)
      have hlens : s.length =
          2 * (pairFstD s).length + 2 +
            (2 * (pairFstD (pairSndD s)).length + 2 + (pairSndD (pairSndD s)).length) := by
        conv_lhs => rw [hs]
        rw [length_pairEncode]
        congr 2
        conv_lhs => rw [ht]
        rw [length_pairEncode]
      have hcd1 : 1 ≤ (pairFstD (pairSndD s)).length :=
        Nat.one_le_iff_ne_zero.mpr (by simpa [List.length_eq_zero_iff] using hcd)
      have hc : c * (pairFstD (pairSndD s)).length =
          c * ((pairFstD (pairSndD s)).length - 1) + c := by
        obtain ⟨m, hm⟩ : ∃ m, (pairFstD (pairSndD s)).length = m + 1 :=
          ⟨_, (Nat.sub_add_cancel hcd1).symm⟩
        rw [hm, Nat.add_sub_cancel]
        ring
      have hl := hlive (pairFstD s) (pairSndD (pairSndD s)) hf
      simp only [pairSndD_pairEncode, pairFstD_pairEncode, length_pairEncode, List.length_drop]
      omega

/-- An orbit envelope from a slack step bound: if every step of `g` respects
`|s| + c·|cd s| ≤ max (·) 2`, then every iterate of `g` from `w` has length at most
`b·(|w|+1)^1` whenever `2 ≤ b` and `c + 1 ≤ b`, the shape
`Complexity.polyTimeComputable_emitIter` consumes (induction, then `|cd w| ≤ |w|`). -/
theorem length_iterate_le_of_slack {g : List Bool → List Bool} (c b : ℕ)
    (hb : 2 ≤ b) (hcb : c + 1 ≤ b)
    (hg : ∀ s, (g s).length + c * (pairFstD (pairSndD (g s))).length ≤
      max (s.length + c * (pairFstD (pairSndD s)).length) 2)
    (w : List Bool) (i : ℕ) :
    (g^[i] w).length ≤ b * (w.length + 1) ^ 1 := by
  have hmax : (g^[i] w).length + c * (pairFstD (pairSndD (g^[i] w))).length ≤
      max (w.length + c * (pairFstD (pairSndD w)).length) 2 := by
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (hg _) (max_le ih (le_max_right _ _))
  have h1 : (pairFstD (pairSndD w)).length ≤ w.length :=
    le_trans (length_pairFstD_le _) (length_pairSndD_le w)
  have h2 : c * (pairFstD (pairSndD w)).length ≤ c * w.length := Nat.mul_le_mul_left c h1
  have h3 : (c + 1) * w.length ≤ b * w.length := Nat.mul_le_mul_right _ hcb
  have h4 : (c + 1) * w.length = c * w.length + w.length := by ring
  rw [pow_one, Nat.mul_add, Nat.mul_one]
  omega

/-- Reading the `i`-th block: on `pairEncode x (u.drop (i·B))`, with `B = a·(|x|+1)^k`,
`sliceTakeAt a k` keeps `x` and the next `B` symbols. -/
theorem sliceTakeAt_pairEncode_drop (a k : ℕ) (x u : List Bool) (i : ℕ) :
    sliceTakeAt a k (pairEncode x (u.drop (i * (a * (x.length + 1) ^ k)))) =
      pairEncode x ((u.drop (i * (a * (x.length + 1) ^ k))).take (a * (x.length + 1) ^ k)) := by
  rw [sliceTakeAt, pairFstD_pairEncode, pairSndD_pairEncode]

/-- Advancing one block: on `pairEncode x (u.drop (i·B))`, with `B = a·(|x|+1)^k`,
`sliceDropAt a k` returns `pairEncode x (u.drop ((i+1)·B))`. -/
theorem sliceDropAt_pairEncode_drop (a k : ℕ) (x u : List Bool) (i : ℕ) :
    sliceDropAt a k (pairEncode x (u.drop (i * (a * (x.length + 1) ^ k)))) =
      pairEncode x (u.drop ((i + 1) * (a * (x.length + 1) ^ k))) := by
  rw [sliceDropAt, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]
  congr 2
  ring

/-- Closed form of a countdown block loop's orbit up to countdown exhaustion: from
`⟨P 0, ⟨1^K, Q 0⟩⟩`, after `i ≤ K` rounds the state is `⟨P i, ⟨1^(K-i), Q i⟩⟩`, given
nonempty heads and the one-round recurrences of the head and the remainder (induction
on `i`: both guards fail and the countdown loses one symbol). -/
theorem orbit {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt)
    (P Q : ℕ → List Bool) {K : ℕ} {s₀ : List Bool}
    (h₀ : s₀ = pairEncode (P 0) (pairEncode (List.replicate K true) (Q 0)))
    (hP : ∀ i ≤ K, P i ≠ [])
    (hupd : ∀ i < K, upd (P i) (Q i) = P (i + 1))
    (hnxt : ∀ i < K, nxt (P i) (Q i) = Q (i + 1))
    {i : ℕ} (hi : i ≤ K) :
    g^[i] s₀ = pairEncode (P i) (pairEncode (List.replicate (K - i) true) (Q i)) := by
  subst hg h₀
  induction i with
  | zero => simp
  | succ i ih =>
    have hii : i < K := hi
    rw [Function.iterate_succ_apply', ih (Nat.le_of_lt hii)]
    have hcd : K - i = (K - (i + 1)) + 1 := by omega
    have hPi : P i ≠ [] := hP i (Nat.le_of_lt hii)
    rw [hcd, List.replicate_succ]
    simp [step, isNilB, hPi, hupd i hii, hnxt i hii]

/-- Once a countdown block loop reaches a live state with empty countdown, every later
iterate is `blockDone`: one more round hits the countdown guard (`step_done`). -/
theorem iterate_done {g : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt)
    {s₀ p q : List Bool} {K : ℕ} (hp : p ≠ [])
    (hK : g^[K] s₀ = pairEncode p (pairEncode [] q)) {i : ℕ} (hi : K < i) :
    g^[i] s₀ = blockDone := by
  subst hg
  obtain ⟨j, rfl⟩ : ∃ j, i = j + (K + 1) := ⟨i - (K + 1), by omega⟩
  rw [Function.iterate_add_apply]
  have hend : (step upd nxt)^[K + 1] s₀ = blockDone := by
    rw [Function.iterate_succ_apply', hK]
    simp [step, isNilB, hp]
  rw [hend]
  clear hi
  induction j with
  | zero => simp
  | succ j ih => rw [Function.iterate_succ_apply', ih, step_done rfl]

/-- Budget domination: `a'·(n+1)^k' < a'·(m+1)^k' + 1` whenever `n ≤ m`. -/
theorem lt_polyBudget_of_le (a' k' : ℕ) {n m : ℕ} (h : n ≤ m) :
    a' * (n + 1) ^ k' < a' * (m + 1) ^ k' + 1 := by
  have := Nat.mul_le_mul_left a' (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) k')
  omega

/-- Single emission: if the orbit of `g` from `s₀` is `⟨P i, ⟨1^(K-i), Q i⟩⟩` with nonempty
heads for `i ≤ K` and `blockDone` afterwards, then over any round budget `N > K` the
concatenated chunks of `emit out` are the one chunk `out ⟨P K, ⟨[], Q K⟩⟩`: only round `K`
emits (`Complexity.flatMap_range_eq_single`). -/
theorem flatMap_emit_orbit {g out : List Bool → List Bool} {s₀ : List Bool}
    (P Q : ℕ → List Bool) {K N : ℕ}
    (horb : ∀ i ≤ K, g^[i] s₀ =
      pairEncode (P i) (pairEncode (List.replicate (K - i) true) (Q i)))
    (hdone : ∀ i, K < i → g^[i] s₀ = blockDone)
    (hKN : K < N) (hP : ∀ i ≤ K, P i ≠ []) :
    (List.range N).flatMap (fun i => emit out (g^[i] s₀)) =
      out (pairEncode (P K) (pairEncode [] (Q K))) := by
  refine flatMap_range_eq_single hKN (fun i _ => ?_)
  rcases Nat.lt_trichotomy i K with hiK | hiK | hiK
  · rw [if_neg (by omega), horb i (le_of_lt hiK)]
    have hne : K - i ≠ 0 := by omega
    simp [emit, isNilB, hP i (le_of_lt hiK), hne]
  · rw [if_pos hiK, hiK, horb K le_rfl, Nat.sub_self, List.replicate_zero]
    simp [emit, isNilB, hP K le_rfl]
  · rw [if_neg (by omega), hdone i hiK]
    simp [emit, blockDone, isNilB]

/-- The output of a countdown block loop from its recurrences: from
`s₀ = ⟨P 0, ⟨1^K, Q 0⟩⟩`, under the hypotheses of `orbit`, the concatenated chunks of
`emit out` over any round budget `N > K` are `out ⟨P K, ⟨[], Q K⟩⟩` (`orbit`,
`iterate_done`, `flatMap_emit_orbit`). -/
theorem loop_output {g out : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} (hg : g = step upd nxt)
    (P Q : ℕ → List Bool) {K N : ℕ} {s₀ : List Bool}
    (h₀ : s₀ = pairEncode (P 0) (pairEncode (List.replicate K true) (Q 0)))
    (hP : ∀ i ≤ K, P i ≠ [])
    (hupd : ∀ i < K, upd (P i) (Q i) = P (i + 1))
    (hnxt : ∀ i < K, nxt (P i) (Q i) = Q (i + 1)) (hKN : K < N) :
    (List.range N).flatMap (fun i => emit out (g^[i] s₀)) =
      out (pairEncode (P K) (pairEncode [] (Q K))) := by
  have horb := fun i (hi : i ≤ K) => orbit hg P Q h₀ hP hupd hnxt hi
  have hK := horb K le_rfl
  rw [Nat.sub_self, List.replicate_zero] at hK
  exact flatMap_emit_orbit P Q horb (fun _ hi => iterate_done hg (hP K le_rfl) hK hi) hKN hP

/-- The headline assembly: if the round `g`, the chunk `e` and the initializer `init` are
polynomial-time, the orbit of `g` has a linear envelope, and the concatenated chunks of
`e` along the orbit from `init z`, over `a'·(|init z|+1)^k' + 1` rounds, are `f z`, then
`f` is polynomial-time (`Complexity.polyTimeComputable_emitIter` after `init`). -/
theorem polyTimeComputable_of_loop {g e init f : List Bool → List Bool}
    (hg : PolyTimeComputable g) (he : PolyTimeComputable e) (hinit : PolyTimeComputable init)
    (a' k' b : ℕ)
    (horbit : ∀ (w : List Bool) (i : ℕ), (g^[i] w).length ≤ b * (w.length + 1) ^ 1)
    (hf : ∀ z, (List.range (a' * ((init z).length + 1) ^ k' + 1)).flatMap
      (fun i => e (g^[i] (init z))) = f z) :
    PolyTimeComputable f := by
  have heq : f = (fun w => (List.range (a' * (w.length + 1) ^ k' + 1)).flatMap
      (fun i => e (g^[i] w))) ∘ init := by
    funext z
    exact (hf z).symm
  rw [heq]
  exact (polyTimeComputable_emitIter hg he a' k' b 1 horbit).comp hinit

/-- **A countdown block loop is polynomial-time.**  For `g = step upd nxt` and `e = emit out`
run from `⟨h₀, ⟨1^(a'(|x z|+1)^k'), r z⟩⟩`: if the updates, `out`, `x`, `r` are polynomial-time,
the live updates obey the slack bound `c`, and the chunks along the orbit are `f z`, then
`f` is polynomial-time (`polyTimeComputable_of_loop`, `length_iterate_le_of_slack`). -/
theorem polyTimeComputable_countdown {g e x r f : List Bool → List Bool}
    {upd nxt : List Bool → List Bool → List Bool} {out : List Bool → List Bool}
    (hg : g = step upd nxt) (he : e = emit out) (h₀ : List Bool) (a' k' c : ℕ)
    (hu : PolyTimeComputable (fun s => upd (pairFstD s) (pairSndD (pairSndD s))))
    (hn : PolyTimeComputable (fun s => nxt (pairFstD s) (pairSndD (pairSndD s))))
    (ho : PolyTimeComputable out) (hx : PolyTimeComputable x) (hr : PolyTimeComputable r)
    (hlive : ∀ h q, h ≠ [] →
      2 * (upd h q).length + (nxt h q).length ≤ 2 * h.length + q.length + 2 + c)
    (hf : ∀ z, (List.range (a' * ((pairEncode h₀ (pairEncode
        (List.replicate (a' * ((x z).length + 1) ^ k') true) (r z))).length + 1) ^ k' + 1)).flatMap
      (fun i => e (g^[i] (pairEncode h₀ (pairEncode
        (List.replicate (a' * ((x z).length + 1) ^ k') true) (r z))))) = f z) :
    PolyTimeComputable f := by
  subst he
  exact polyTimeComputable_of_loop (polyTimeComputable_step hg hu hn)
    (polyTimeComputable_emit ho) (polyTimeComputable_countdownInit h₀ hx hr a' k') a' k'
    (c + 2) (length_iterate_le_of_slack c (c + 2) (by omega) (by omega)
      (length_step_le hg c hlive)) hf

end BlockLoop

/-! ### Truncating bitwise XOR -/

/-- Bitwise XOR of the two components of a pair, truncating to the shorter
component (`List.zipWith` semantics); malformed pairs give `[]`. -/
def xorD (z : List Bool) : List Bool :=
  List.zipWith xor (pairFstD z) (pairSndD z)

/-- One round of the XOR transducer: drop the head of both components. -/
private def xorPairStep (s : List Bool) : List Bool :=
  pairEncode ((pairFstD s).drop 1) ((pairSndD s).drop 1)

/-- The XOR transducer's chunk: one XOR bit while both components are
nonempty, nothing afterwards. -/
private def xorPairEmit (s : List Bool) : List Bool :=
  if isNilB (pairFstD s) || isNilB (pairSndD s) then []
  else if (pairFstD s).headD false then
    if (pairSndD s).headD false then [false] else [true]
  else
    if (pairSndD s).headD false then [true] else [false]

private theorem polyTimeComputable_xorPairStep : PolyTimeComputable xorPairStep := by
  have h₁ := polyTimeComputable_tail.comp polyTimeComputable_pairFstD
  have h₂ := polyTimeComputable_tail.comp polyTimeComputable_pairSndD
  exact h₁.pairEncode h₂

private theorem polyTimeComputable_xorPairEmit : PolyTimeComputable xorPairEmit := by
  have hguard : PolyTimeComputable (fun s =>
      [isNilB (pairFstD s) || isNilB (pairSndD s)]) :=
    polyTimeComputable_or (polyTimeComputable_isNil.comp polyTimeComputable_pairFstD)
      (polyTimeComputable_isNil.comp polyTimeComputable_pairSndD)
  have hd1 : PolyTimeComputable (fun s => [(pairFstD s).headD false]) :=
    polyTimeComputable_headD.comp polyTimeComputable_pairFstD
  have hd2 : PolyTimeComputable (fun s => [(pairSndD s).headD false]) :=
    polyTimeComputable_headD.comp polyTimeComputable_pairSndD
  exact polyTimeComputable_ite hguard (polyTimeComputable_const [])
    (polyTimeComputable_ite hd1
      (polyTimeComputable_ite hd2 (polyTimeComputable_const [false])
        (polyTimeComputable_const [true]))
      (polyTimeComputable_ite hd2 (polyTimeComputable_const [true])
        (polyTimeComputable_const [false])))

/-- One XOR round never grows the state beyond `max` with the empty pair
(`length_pairEncode_drop_le` with one letter dropped from each component). -/
private theorem length_xorPairStep_le (s : List Bool) :
    (xorPairStep s).length ≤ max s.length 2 :=
  length_pairEncode_drop_le s 1 1

/-- The XOR transducer's orbit drops both components one symbol per round. -/
private theorem xorPairStep_orbit (p u : List Bool) (i : ℕ) :
    xorPairStep^[i] (pairEncode p u) = pairEncode (p.drop i) (u.drop i) := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [xorPairStep, pairFstD_pairEncode, pairSndD_pairEncode, List.drop_drop]

/-- On two nonempty components the chunk is the single XOR bit of the heads. -/
private theorem xorPairEmit_cons (b c : Bool) (p u : List Bool) :
    xorPairEmit (pairEncode (b :: p) (c :: u)) = [xor b c] := by
  cases b <;> cases c <;> simp [xorPairEmit, isNilB]

/-- Once a component is exhausted the chunk is empty. -/
private theorem xorPairEmit_nil {p u : List Bool} (h : p = [] ∨ u = []) :
    xorPairEmit (pairEncode p u) = [] := by
  rcases h with rfl | rfl <;> simp [xorPairEmit, isNilB]

/-- The concatenated chunks of the XOR transducer compute `List.zipWith xor`.
**Proof sketch.** Induction on the round budget, generalizing the two
components: each cons-cons round contributes its head XOR
(`xorPairEmit_cons`) and the orbit shifts both tails; an exhausted component
silences every later round. -/
private theorem xorPair_output : ∀ (N : ℕ) (p u : List Bool),
    min p.length u.length ≤ N →
    (List.range N).flatMap (fun i => xorPairEmit (pairEncode (p.drop i) (u.drop i))) =
      List.zipWith xor p u := by
  intro N
  induction N with
  | zero =>
    intro p u h
    have : p = [] ∨ u = [] := by
      rcases p with _ | ⟨b, p⟩
      · exact Or.inl rfl
      rcases u with _ | ⟨c, u⟩
      · exact Or.inr rfl
      simp at h
    rcases this with rfl | rfl <;> simp
  | succ N ih =>
    intro p u h
    rw [List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    rcases p with _ | ⟨b, p⟩
    · simp only [List.zipWith_nil_left, List.drop_nil]
      rw [xorPairEmit_nil (Or.inl rfl), List.nil_append]
      refine List.flatMap_eq_nil_iff.mpr (fun i _ => ?_)
      exact xorPairEmit_nil (Or.inl rfl)
    rcases u with _ | ⟨c, u⟩
    · simp only [List.zipWith_nil_right, List.drop_nil]
      rw [xorPairEmit_nil (Or.inr rfl), List.nil_append]
      refine List.flatMap_eq_nil_iff.mpr (fun i _ => ?_)
      exact xorPairEmit_nil (Or.inr rfl)
    rw [List.drop_zero, List.drop_zero, xorPairEmit_cons, List.zipWith_cons_cons]
    have hrest : (List.range N).flatMap
        (fun i => xorPairEmit (pairEncode ((b :: p).drop (i + 1)) ((c :: u).drop (i + 1)))) =
        List.zipWith xor p u := by
      have heq : (fun i => xorPairEmit (pairEncode ((b :: p).drop (i + 1))
          ((c :: u).drop (i + 1)))) =
          (fun i => xorPairEmit (pairEncode (p.drop i) (u.drop i))) := by
        funext i
        rfl
      rw [heq]
      exact ih p u (by simp at h; omega)
    rw [hrest]
    rfl

/-- `xorD` is polynomial-time computable.
**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`, assembled
by `Complexity.BlockLoop.polyTimeComputable_of_loop`, with the orbit envelope from
`Complexity.BlockLoop.length_iterate_le_of_slack`: the loop state is the pair of
not-yet-consumed components; each round emits
the XOR of the two head bits (nothing once either component is exhausted) and
drops both heads, so the concatenated output is exactly the truncating
`List.zipWith xor`.  The round budget is the normalized pair's length plus two,
`(pairEncode (pairFstD z) (pairSndD z)).length + 2`, which dominates the shorter
component's length.  (The truncating semantics on unequal lengths is the
audited ch7-phase1 finding 1 convention.) -/
theorem polyTimeComputable_xorD : PolyTimeComputable xorD := by
  refine BlockLoop.polyTimeComputable_of_loop polyTimeComputable_xorPairStep
    polyTimeComputable_xorPairEmit
    (polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD) 1 1 2
    (BlockLoop.length_iterate_le_of_slack 0 2 (by omega) (by omega)
      (fun s => by simpa using length_xorPairStep_le s)) (fun z => ?_)
  have hbudget : min (pairFstD z).length (pairSndD z).length ≤
      1 * ((pairEncode (pairFstD z) (pairSndD z)).length + 1) ^ 1 + 1 := by
    have h1 := length_pairFstD_le z
    rw [pow_one, length_pairEncode]
    omega
  simp only [xorPairStep_orbit]
  exact xorPair_output _ (pairFstD z) (pairSndD z) hbudget

/-- `xorD` computes the truncating bitwise XOR on genuine pairs. -/
@[simp]
theorem xorD_pairEncode (a b : List Bool) :
    xorD (pairEncode a b) = List.zipWith xor a b := by
  simp [xorD]

end Complexity
