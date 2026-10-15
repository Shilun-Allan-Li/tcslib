/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.ClassPSPACE.TQBFHardMachine
import TCSlib.Complexity.ClassNP.PolyTimePairing
import TCSlib.Complexity.TuringMachine.Build.Primitives
import TCSlib.Complexity.ClassNP.PolyTimeBlockTests
import TCSlib.Complexity.ClassNP.PolyTimePrefix
import TCSlib.Complexity.ClassNP.Transducer
import TCSlib.Complexity.ClassP.P
import TCSlib.Complexity.SpaceComplexity.ConfigCount
import TCSlib.Complexity.SpaceComplexity.Codec.Deciders
import TCSlib.Complexity.SpaceComplexity.Codec.StepDecider

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The polynomial-time verifier of the `TQBF` matrix

The `TQBF` reduction writes the matrix of its quantified formula as a circuit, the uniform
tableau of a polynomial-time machine (`Complexity.cfgTab`). This file builds that machine's
function: `predB y`, on `y = ⟨x, σ⟩` with `σ` an assignment of the prefix variables, checks

* the code-word prefix of the block at `w` is the initial code (`Complexity.Codec.initLang`),
* the code-word prefix of the block at `2w` is an accepting code (`Complexity.Codec.acceptLang`),
* and either the pair of the innermost record is one step (equal blocks, or code prefixes
  forming a step pair, `Complexity.Codec.stepLang`), or some record's pair is not selected
  by its parent's pair and midpoint (the flat form of the `ψ` matrix,
  `Complexity.TQBFHard.levelMatrix_iff_flat`).

The block width is `w = A (n + 1)^a` and the window radius `2d (n + 1)^c`, for parameters
fixed by the reduction. `predB` is polynomial-time (`polyTimeComputable_predB`): the three
code languages are in `L ⊆ P` (`Complexity.LOGSPACE_subset_P`), blocks are cut out by the
length-gated prefix operations, the radius is converted to binary by the library's
linear-time binary length counter (`Turing.FinTM.computesFunInTime_lengthBits` with
`Complexity.polyTimeComputable_of_linear`), and the disjunction over records is the OR-flag
block loop `Complexity.BlockLoop.polyTimeComputable_orLoop`. On an input whose second
component is an assignment of the prefix variables, it is the flat matrix
(`Complexity.TQBFHard.predB_iff`, in `TQBFHardBridge`).

Infrastructure for `Complexity.TQBF_PSPACEHard`; not itself a book result. [AB09, Theorem
4.13]'s proof says the formula "can be computed in polynomial time" without detail; this is
that computation's matrix half.

## Main definitions

* `Complexity.TQBFHard.predB` — the verifier.

## Main results

* `Complexity.TQBFHard.polyTimeComputable_predB` — the verifier is polynomial-time.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.2, Theorem 4.13; §4.1, `L ⊆ P`, p. 112.)
-/

namespace Complexity

namespace TQBFHard

open Turing Codec

/-! ### Polynomial-time building blocks -/

/-- Dropping a polynomial-time unary amount from a polynomial-time word is polynomial-time
(`Complexity.PrefixByLength.drop`). -/
theorem pt_drop {o : List Bool → ℕ} {S : List Bool → List Bool}
    (ho : PolyTimeComputable fun y => List.replicate (o y) true) (hS : PolyTimeComputable S) :
    PolyTimeComputable fun y => (S y).drop (o y) := by
  have := polyTimeComputable_dropPrefixByLength.comp (ho.pairEncode hS)
  convert this using 1
  funext y
  simp [Function.comp, PrefixByLength.drop]

/-- Taking a polynomial-time unary amount of a polynomial-time word is polynomial-time
(`Complexity.PrefixByLength.take`). -/
theorem pt_take {o : List Bool → ℕ} {S : List Bool → List Bool}
    (ho : PolyTimeComputable fun y => List.replicate (o y) true) (hS : PolyTimeComputable S) :
    PolyTimeComputable fun y => (S y).take (o y) := by
  have := polyTimeComputable_takePrefixByLength.comp (ho.pairEncode hS)
  convert this using 1
  funext y
  simp [Function.comp, PrefixByLength.take]

/-- A fixed multiple of the length of a polynomial-time word, in unary, is polynomial-time. -/
theorem pt_rep_mul (k : ℕ) {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable fun y => List.replicate (k * (g y).length) true := by
  induction k with
  | zero => simpa using polyTimeComputable_const []
  | succ k ih =>
    have := ih.append (polyTimeComputable_unary.comp hg)
    convert this using 1
    funext y
    rw [Nat.succ_mul, List.replicate_add]
    rfl

/-- The one-pass filter keeping the `1`s of a word. -/
def keepTrue (l : List Bool) : List Bool :=
  transduce (σ := Unit) (fun _ _ => ()) (fun _ b => if b then some true else none) () l

/-- The filter is empty iff the word has no `1`. -/
theorem keepTrue_eq_nil_iff (l : List Bool) : keepTrue l = [] ↔ ∀ b ∈ l, b = false := by
  induction l with
  | nil => simp [keepTrue, transduce]
  | cons b l ih =>
    cases b
    · simpa [keepTrue, transduce] using ih
    · simp [keepTrue, transduce]

/-- Two words are equal iff they have the same length and their bitwise XOR has no `1`. -/
theorem eq_iff_xor (u v : List Bool) :
    u = v ↔ u.length = v.length ∧ ∀ b ∈ List.zipWith xor u v, b = false := by
  induction u generalizing v with
  | nil => cases v <;> simp
  | cons a u ih =>
    cases v with
    | nil => simp
    | cons b v =>
      simp only [List.cons.injEq, List.length_cons, Nat.add_right_cancel_iff,
        List.zipWith_cons_cons, List.mem_cons, forall_eq_or_imp, ih v]
      cases a <;> cases b <;> simp

/-- **Equality of two polynomial-time words is polynomial-time** (as a one-bit verdict):
the length test (`Complexity.polyTimeComputable_lenEq`) and the emptiness test of the
`1`s of the bitwise XOR (`Complexity.polyTimeComputable_xorD`). -/
theorem pt_eq {f g : List Bool → List Bool} (hf : PolyTimeComputable f)
    (hg : PolyTimeComputable g) : PolyTimeComputable fun y => [decide (f y = g y)] := by
  have hp := hf.pairEncode hg
  have h1 := polyTimeComputable_lenEq.comp hp
  have h2 := (polyTimeComputable_isNil.comp
    ((polyTimeComputable_transduce (σ := Unit) (fun _ _ => ())
      (fun _ b => if b then some true else none) ()).comp
      (polyTimeComputable_xorD.comp hp)))
  have h := polyTimeComputable_and h1 h2
  convert h using 1
  funext y
  simp only [Function.comp, pairFstD_pairEncode, pairSndD_pairEncode, xorD_pairEncode]
  congr 1
  rw [Bool.eq_iff_iff, Bool.and_eq_true, decide_eq_true_iff, decide_eq_true_iff,
    decide_eq_true_iff, eq_iff_xor (f y) (g y)]
  exact and_congr_right fun _ => (keepTrue_eq_nil_iff _).symm

/-- **A logarithmic-space language has a polynomial-time indicator** (`L ⊆ P`,
`Complexity.LOGSPACE_subset_P`, with `Complexity.mem_P_iff`). -/
theorem pt_indicator {L : Language Bool} (hL : L ∈ LOGSPACE) :
    PolyTimeComputable fun z => [MultiTapeTM.indicator L z] := by
  obtain ⟨C, c, M, hM⟩ := mem_P_iff.mp (LOGSPACE_subset_P hL)
  exact ⟨M, C, c, hM⟩

/-! ### The parameters and the verifier -/

variable (N : FinNDTM Bool) (d c A a : ℕ)

/-- The window radius `2d (n + 1)^c` at input length `n`. -/
def vrad (n : ℕ) : ℕ := 2 * d * (n + 1) ^ c

/-- The block width `A (n + 1)^a` at input length `n`. -/
def vwid (n : ℕ) : ℕ := A * (n + 1) ^ a

/-- The code-word length at input length `n` and radius `vrad n`. -/
def vlen (n : ℕ) : ℕ := codeLen N n (vrad d c n)

/-- The code-word prefix of the block at offset `off` of the assignment part of `y`. -/
def cpAt (y : List Bool) (off : ℕ) : List Bool :=
  ((pairSndD y).drop off).take (vlen N d c (pairFstD y).length)

/-- The block at offset `off` of the assignment part of `y`. -/
def blkAt (y : List Bool) (off : ℕ) : List Bool :=
  ((pairSndD y).drop off).take (vwid A a (pairFstD y).length)

/-- The initial-code test on the block at `w`. -/
noncomputable def initB (y : List Bool) : Bool :=
  MultiTapeTM.indicator (initLang N) (pairEncode (pairFstD y)
    (pairEncode (cpAt N d c y (vwid A a (pairFstD y).length))
      (Nat.bits (vrad d c (pairFstD y).length))))

/-- The accepting-code test on the block at `2w`. -/
noncomputable def accB (y : List Bool) : Bool :=
  MultiTapeTM.indicator (acceptLang N) (pairEncode (pairFstD y)
    (pairEncode (cpAt N d c y (2 * vwid A a (pairFstD y).length))
      (Nat.bits (vrad d c (pairFstD y).length))))

/-- The one-step test on the innermost record's pair (record `w`, blocks at `3w·w + w` and
`3w·w + 2w`): equal blocks, or code prefixes forming a step pair. -/
noncomputable def baseB (y : List Bool) : Bool :=
  let w := vwid A a (pairFstD y).length
  decide (blkAt A a y (3 * w * w + w) = blkAt A a y (3 * w * w + 2 * w)) ||
    MultiTapeTM.indicator (stepLang N) (pairEncode (pairFstD y)
      (pairEncode (cpAt N d c y (3 * w * w + w)) (pairEncode (cpAt N d c y (3 * w * w + 2 * w))
        (Nat.bits (vrad d c (pairFstD y).length)))))

/-- The block `k` of a window `⟨⟨x, 1^w⟩, rest⟩`: the `w` letters of `rest` from `k w`. -/
def winBlk (q : List Bool) (k : ℕ) : List Bool :=
  ((pairSndD q).drop (k * (pairSndD (pairFstD q)).length)).take
    (pairSndD (pairFstD q)).length

/-- **The selection test on a window** `⟨⟨x, 1^w⟩, rest⟩` whose `rest` starts with two
records `Z, A, B, Z', U', V'` (blocks `0, …, 5`): `(U', V') = (A, Z')` or `(Z', B)`. -/
def selT (q : List Bool) : Bool :=
  (decide (winBlk q 4 = winBlk q 1) && decide (winBlk q 5 = winBlk q 3)) ||
    (decide (winBlk q 4 = winBlk q 3) && decide (winBlk q 5 = winBlk q 2))

/-- The window of record `j`: the header `⟨x, 1^w⟩` and the assignment from `3wj`. -/
def lvlQ (y : List Bool) (j : ℕ) : List Bool :=
  pairEncode (pairEncode (pairFstD y) (List.replicate (vwid A a (pairFstD y).length) true))
    ((pairSndD y).drop (3 * vwid A a (pairFstD y).length * j))

/-- Some record `j < w` has its successor not selected. -/
def orB (y : List Bool) : Bool :=
  (List.range (vwid A a (pairFstD y).length)).any fun j => !selT (lvlQ A a y j)

/-- **The verifier**: initial block, accepting block, and the flat `ψ` matrix. -/
noncomputable def predB (y : List Bool) : Bool :=
  initB N d c A a y && accB N d c A a y && (baseB N d c A a y || orB A a y)

/-! ### Polynomial time -/

/-- The block width in unary. -/
theorem pt_vwid : PolyTimeComputable fun y => List.replicate (vwid A a (pairFstD y).length) true :=
  (polyTimeComputable_polyUnary A a).comp polyTimeComputable_pairFstD

/-- A fixed multiple, plus a fixed multiple of the square, of the block width, in unary. -/
theorem pt_vwid_lin (k l : ℕ) : PolyTimeComputable fun y =>
    List.replicate (k * vwid A a (pairFstD y).length * vwid A a (pairFstD y).length +
      l * vwid A a (pairFstD y).length) true := by
  have h1 : PolyTimeComputable fun y =>
      List.replicate (k * A * A * ((pairFstD y).length + 1) ^ (a + a)) true :=
    (polyTimeComputable_polyUnary (k * A * A) (a + a)).comp polyTimeComputable_pairFstD
  have h2 : PolyTimeComputable fun y =>
      List.replicate (l * A * ((pairFstD y).length + 1) ^ a) true :=
    (polyTimeComputable_polyUnary (l * A) a).comp polyTimeComputable_pairFstD
  convert h1.append h2 using 1
  funext y
  rw [← List.replicate_add]
  congr 1
  simp only [vwid, pow_add]
  ring

/-- The radius in binary. -/
theorem pt_bits_vrad : PolyTimeComputable fun y => Nat.bits (vrad d c (pairFstD y).length) := by
  have := (polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
    ((polyTimeComputable_polyUnary (2 * d) c).comp polyTimeComputable_pairFstD)
  convert this using 1
  funext y
  simp [vrad]

/-- The code-word length in unary: `4dW (n + 1)^c + (W + 1) + |bits (n + 1)|`. -/
theorem pt_vlen :
    PolyTimeComputable fun y => List.replicate (vlen N d c (pairFstD y).length) true := by
  have h1 : PolyTimeComputable fun y =>
      List.replicate (4 * d * W N * ((pairFstD y).length + 1) ^ c) true :=
    (polyTimeComputable_polyUnary (4 * d * W N) c).comp polyTimeComputable_pairFstD
  have h2 : PolyTimeComputable fun _ : List Bool => List.replicate (W N + 1) true :=
    polyTimeComputable_const _
  have h3 : PolyTimeComputable fun y =>
      List.replicate (Nat.bits ((pairFstD y) ++ [true]).length).length true :=
    polyTimeComputable_unary.comp
      ((polyTimeComputable_of_linear FinTM.computesFunInTime_lengthBits).comp
        (polyTimeComputable_pairFstD.append (polyTimeComputable_const [true])))
  convert (h1.append h2).append h3 using 1
  funext y
  rw [← List.replicate_add, ← List.replicate_add]
  congr 1
  simp only [vlen, codeLen, vrad, wP, List.length_append, List.length_singleton]
  ring

/-- Code-word prefixes at a polynomial-time unary offset are polynomial-time. -/
theorem pt_cpAt {o : List Bool → ℕ} (ho : PolyTimeComputable fun y => List.replicate (o y) true) :
    PolyTimeComputable fun y => cpAt N d c y (o y) :=
  pt_take (pt_vlen N d c) (pt_drop ho polyTimeComputable_pairSndD)

/-- Blocks at a polynomial-time unary offset are polynomial-time. -/
theorem pt_blkAt {o : List Bool → ℕ} (ho : PolyTimeComputable fun y => List.replicate (o y) true) :
    PolyTimeComputable fun y => blkAt A a y (o y) :=
  pt_take (pt_vwid A a) (pt_drop ho polyTimeComputable_pairSndD)

/-- The initial-code test is polynomial-time. -/
theorem pt_initB : PolyTimeComputable fun y => [initB N d c A a y] := by
  have hcp := pt_cpAt N d c (pt_vwid A a)
  exact (pt_indicator (initLang_mem (N := N))).comp (polyTimeComputable_pairFstD.pairEncode
    (hcp.pairEncode (pt_bits_vrad d c)))

/-- The accepting-code test is polynomial-time. -/
theorem pt_accB : PolyTimeComputable fun y => [accB N d c A a y] := by
  have h2 : PolyTimeComputable fun y =>
      List.replicate (2 * vwid A a (pairFstD y).length) true := by
    have := pt_vwid_lin A a 0 2
    simpa using this
  have hcp := pt_cpAt N d c h2
  exact (pt_indicator (acceptLang_mem (N := N))).comp (polyTimeComputable_pairFstD.pairEncode
    (hcp.pairEncode (pt_bits_vrad d c)))

/-- The innermost one-step test is polynomial-time. -/
theorem pt_baseB : PolyTimeComputable fun y => [baseB N d c A a y] := by
  have hu := pt_vwid_lin A a 3 1
  have hv := pt_vwid_lin A a 3 2
  simp only [Nat.one_mul] at hu
  have heq := pt_eq (pt_blkAt A a hu) (pt_blkAt A a hv)
  have hst := (pt_indicator (stepLang_mem (N := N))).comp (polyTimeComputable_pairFstD.pairEncode
    ((pt_cpAt N d c hu).pairEncode ((pt_cpAt N d c hv).pairEncode (pt_bits_vrad d c))))
  exact polyTimeComputable_or heq hst

/-- The selection test on a window is polynomial-time. -/
theorem pt_selT : PolyTimeComputable fun q => [selT q] := by
  have hone : PolyTimeComputable fun q => pairSndD (pairFstD q) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hblk (k : ℕ) : PolyTimeComputable fun q => winBlk q k := by
    have hw : PolyTimeComputable fun q =>
        List.replicate (pairSndD (pairFstD q)).length true := polyTimeComputable_unary.comp hone
    exact pt_take hw (pt_drop (pt_rep_mul k hone) polyTimeComputable_pairSndD)
  exact polyTimeComputable_or
    (polyTimeComputable_and (pt_eq (hblk 4) (hblk 1)) (pt_eq (hblk 5) (hblk 3)))
    (polyTimeComputable_and (pt_eq (hblk 4) (hblk 3)) (pt_eq (hblk 5) (hblk 2)))

/-- The record step of the OR loop: drop one record (`3w` letters) from a window. -/
def nxtW (q : List Bool) : List Bool :=
  pairEncode (pairFstD q) ((pairSndD q).drop (3 * (pairSndD (pairFstD q)).length))

/-- The disjunction over records is polynomial-time.

**Proof sketch.** The OR-flag block loop (`Complexity.BlockLoop.polyTimeComputable_orLoop`)
over the `w = A (n + 1)^a` windows `lvlQ y j`, advancing by `nxtW` (which drops one record)
and testing `!selT`; the windows are polynomial-time (`pt_drop`, `pt_vwid`) and `nxtW` does
not lengthen them. -/
theorem pt_orB : PolyTimeComputable fun y => [orB A a y] := by
  have hone : PolyTimeComputable fun q => pairSndD (pairFstD q) :=
    polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD
  have hnxt : PolyTimeComputable nxtW :=
    polyTimeComputable_pairFstD.pairEncode
      (pt_drop (pt_rep_mul 3 hone) polyTimeComputable_pairSndD)
  have hQ0 : PolyTimeComputable fun y => lvlQ A a y 0 := by
    have : PolyTimeComputable fun y =>
        pairEncode (pairEncode (pairFstD y) (List.replicate (vwid A a (pairFstD y).length) true))
          (pairSndD y) :=
      (polyTimeComputable_pairFstD.pairEncode (pt_vwid A a)).pairEncode
        polyTimeComputable_pairSndD
    simpa [lvlQ] using this
  have h := BlockLoop.polyTimeComputable_orLoop (t := fun q => !selT q) (nxt := nxtW)
    (x := pairFstD) (r := fun y => lvlQ A a y 0) (lvlQ A a) (F := fun y j => !selT (lvlQ A a y j))
    A a 0 ((polyTimeComputable_not pt_selT).comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
    (hnxt.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))
    polyTimeComputable_pairFstD hQ0
    (fun q => by
      have := length_pair_components_le q
      simp only [nxtW, length_pairEncode, List.length_drop]
      omega)
    (fun y => by simp only [lvlQ, length_pairEncode]; omega)
    (fun y => rfl)
    (fun y i _ => by
      simp only [nxtW, lvlQ, pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate,
        List.drop_drop]
      congr 2)
    (fun y i _ => rfl)
  simpa [orB, vwid] using h

/-- **The verifier is polynomial-time.** (Conjunction and disjunction of the polynomial-time
tests `pt_initB`, `pt_accB`, `pt_baseB`, `pt_orB`.) -/
theorem polyTimeComputable_predB : PolyTimeComputable fun y => [predB N d c A a y] :=
  polyTimeComputable_and (polyTimeComputable_and (pt_initB N d c A a) (pt_accB N d c A a))
    (polyTimeComputable_or (pt_baseB N d c A a) (pt_orB A a))

end TQBFHard

end Complexity
