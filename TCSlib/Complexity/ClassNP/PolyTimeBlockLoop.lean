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
  polynomial-time, via the emit-iteration loop.
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

private theorem polyTimeComputable_xorPairStep : PolyTimeComputable xorPairStep :=
  (polyTimeComputable_tail.comp polyTimeComputable_pairFstD).pairEncode
    (polyTimeComputable_tail.comp polyTimeComputable_pairSndD)

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

/-- One XOR round never grows the state beyond `max` with the empty pair. -/
private theorem length_xorPairStep_le (s : List Bool) :
    (xorPairStep s).length ≤ max s.length 2 := by
  cases h : pairDecode s with
  | none =>
    have h1 : pairFstD s = [] := by simp [pairFstD, h]
    have h2 : pairSndD s = [] := by simp [pairSndD, h]
    refine le_trans ?_ (le_max_right _ _)
    simp [xorPairStep, h1, h2, length_pairEncode]
  | some ab =>
    obtain ⟨a, b⟩ := ab
    have hz := eq_pairEncode_of_pairDecode s a b h
    refine le_trans ?_ (le_max_left _ _)
    rw [hz]
    simp only [xorPairStep, pairFstD_pairEncode, pairSndD_pairEncode, length_pairEncode,
      List.length_drop]
    omega

/-- Orbit envelope for the XOR transducer. -/
private theorem length_xorPairStep_iterate (w : List Bool) (i : ℕ) :
    (xorPairStep^[i] w).length ≤ 2 * (w.length + 1) ^ 1 := by
  have hmax : (xorPairStep^[i] w).length ≤ max w.length 2 := by
    induction i with
    | zero => simpa using le_max_left _ _
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (length_xorPairStep_le _) (max_le ih (le_max_right _ _))
  refine le_trans hmax ?_
  rw [pow_one]
  exact max_le (by omega) (by omega)

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
**Proof sketch.** An instance of `Complexity.polyTimeComputable_emitIter`:
the loop state is the pair of not-yet-consumed components; each round emits
the XOR of the two head bits (nothing once either component is exhausted) and
drops both heads, so the concatenated output is exactly the truncating
`List.zipWith xor`.  The round budget `|z|+1` dominates the shorter
component's length.  (The truncating semantics on unequal lengths is the
audited ch7-phase1 finding 1 convention.) -/
theorem polyTimeComputable_xorD : PolyTimeComputable xorD := by
  have hloop := polyTimeComputable_emitIter polyTimeComputable_xorPairStep
    polyTimeComputable_xorPairEmit 1 1 2 1 (fun w i => length_xorPairStep_iterate w i)
  have hinit : PolyTimeComputable (fun z => pairEncode (pairFstD z) (pairSndD z)) :=
    polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD
  have heq : xorD = (fun w => (List.range (1 * (w.length + 1) ^ 1 + 1)).flatMap
      (fun i => xorPairEmit (xorPairStep^[i] w))) ∘
      (fun z => pairEncode (pairFstD z) (pairSndD z)) := by
    funext z
    rw [Function.comp_apply]
    have horb : ∀ i, xorPairStep^[i] (pairEncode (pairFstD z) (pairSndD z)) =
        pairEncode ((pairFstD z).drop i) ((pairSndD z).drop i) :=
      xorPairStep_orbit (pairFstD z) (pairSndD z)
    have hbudget : min (pairFstD z).length (pairSndD z).length ≤
        1 * ((pairEncode (pairFstD z) (pairSndD z)).length + 1) ^ 1 + 1 := by
      have h1 := length_pairFstD_le z
      rw [pow_one, length_pairEncode]
      omega
    calc xorD z = List.zipWith xor (pairFstD z) (pairSndD z) := rfl
      _ = (List.range (1 * ((pairEncode (pairFstD z) (pairSndD z)).length + 1) ^ 1 + 1)).flatMap
          (fun i => xorPairEmit (pairEncode ((pairFstD z).drop i) ((pairSndD z).drop i))) :=
        (xorPair_output _ (pairFstD z) (pairSndD z) hbudget).symm
      _ = _ := by
        simp only [horb]
  rw [heq]
  exact hloop.comp hinit

/-- `xorD` computes the truncating bitwise XOR on genuine pairs. -/
@[simp]
theorem xorD_pairEncode (a b : List Bool) :
    xorD (pairEncode a b) = List.zipWith xor a b := by
  simp [xorD]

end Complexity
