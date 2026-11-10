/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Experiments
import TCSlib.Cryptography.SIS.Encoding
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Complexity.ClassP.BinaryArith.Loops

import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Raw collision outputs to exact signed SIS solutions

## Main definitions

* `rawCollisionInputs`: use existing false-padding/truncation and prefix splitting.
* `collisionOutputStep`, `collisionOutputPoly`: write signed integer bit differences.

## Main results

The raw postprocessor has an exact unconditional output width, writes the existing
signed encoder's output, and parses to the actual integer difference whenever one
magnitude bit fits. A same-coin probability bound retains arbitrary finder outputs.
The polynomial-time postprocessor composes its leaf step with the registered counted loop.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  observations after Equation (4.1.1) (binary collisions give short integer relations).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Section 2.1 (binary machine outputs).

Padding and signed output are disclosed repository representation conventions.
This module bridges raw strings to the existing typed collision/SIS experiments;
it does not assert that a generic CRH primitive bridge or an independent SIS hardness
assumption has been discharged. No general signed subtraction machine is needed.
-/

namespace TCSlib.Cryptography.Hashing.SIS

open Complexity Turing
open Encoding.BinaryArith

/-- Pad or truncate a raw word to `m+m` bits and split it into two domain words.
Missing bits are false and excess bits are ignored, using existing public conventions. -/
@[simps! (config := { isSimp := false }) fst snd]
def rawCollisionInputs (m : ℕ) (raw : List Bool) :
    (Fin m → Bool) × (Fin m → Bool) :=
  splitCoins m m (padFin (m + m) raw)

/-- The complete raw interpretation uses the original `padFin` and `splitCoins` maps. -/
theorem rawCollisionInputs_eq (m : ℕ) (raw : List Bool) :
    rawCollisionInputs m raw = splitCoins m m (padFin (m + m) raw) := rfl

/-- Emit one sign/magnitude block for the integer difference of the next two bits.
Zero has a false sign; only the false/true pair has a negative sign. -/
def collisionOutputStep (z : List Bool) : List Bool :=
  let c := pairFstD z
  let xs := pairFstD (pairSndD z)
  let ys := pairFstD (pairSndD (pairSndD z))
  let out := pairSndD (pairSndD (pairSndD z))
  let x := xs.headD false
  let y := ys.headD false
  let magnitude := normalizeWidthPoly .var (pairEncode c [Bool.xor x y])
  pairEncode c (pairEncode (xs.drop 1)
    (pairEncode (ys.drop 1) (out ++ ((!x && y) :: magnitude))))

/-- The complete output step writes sign `!x && y` and the normalized xor magnitude. -/
theorem collisionOutputStep_eq (z : List Bool) :
    collisionOutputStep z =
      let c := pairFstD z
      let xs := pairFstD (pairSndD z)
      let ys := pairFstD (pairSndD (pairSndD z))
      let out := pairSndD (pairSndD (pairSndD z))
      let x := xs.headD false
      let y := ys.headD false
      let magnitude := normalizeWidthPoly .var (pairEncode c [Bool.xor x y])
      pairEncode c (pairEncode (xs.drop 1)
        (pairEncode (ys.drop 1) (out ++ ((!x && y) :: magnitude)))) := rfl

/-- The signed-output step retains the entire magnitude-width context.

**Proof sketch.** Read the step equation and apply the public pair-first equation. -/
theorem collisionOutputStep_fst (z : List Bool) :
    pairFstD (collisionOutputStep z) = pairFstD z := by
  rw [collisionOutputStep_eq, pairFstD_pairEncode]

/-- One signed-output step grows linearly in the retained magnitude width.

**Proof sketch.** Both bit suffixes shrink and the output appends one sign plus
exactly the retained number of magnitude bits. Public pairing lengths cover malformed
framing with the stated constant slack. -/
theorem collisionOutputStep_length_le (z : List Bool) :
    (collisionOutputStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  have houter := length_pair_components_le z
  have hmiddle := length_pair_components_le (pairSndD z)
  have hinner := length_pair_components_le (pairSndD (pairSndD z))
  simp only [collisionOutputStep_eq, length_pairEncode, List.length_drop, List.length_append,
    List.length_cons, normalizeWidthPoly_length, pairFstD_pairEncode, PolyExpr.eval_var]
  omega

/-- The signed-output leaf step is polynomial-time.

**Proof sketch.** Compose the public head/default, Boolean not/and/xor, cons,
append, drop and pairing machines with `normalizeWidthPoly .var`. These are leaf
operations; no signed arithmetic, hash evaluation or collision test is performed. -/
theorem polyTimeComputable_collisionOutputStep : PolyTimeComputable collisionOutputStep := by
  have hc := polyTimeComputable_pairFstD
  have hxs := BinArith.polyTimeComputable_slot2
  have hys := polyTimeComputable_pairFstD.comp BinArith.polyTimeComputable_slot3
  have hout := BinArith.polyTimeComputable_slot4
  have hx := polyTimeComputable_headD.comp hxs
  have hy := polyTimeComputable_headD.comp hys
  have hsign := polyTimeComputable_and (polyTimeComputable_not hx) hy
  have hmagnitude := (polyTimeComputable_normalizeWidthPoly .var).comp
    (hc.pairEncode (BinArith.polyTimeComputable_xor hx hy))
  have hblock := BinArith.polyTimeComputable_cons hsign hmagnitude
  have hxDrop := polyTimeComputable_tail.comp hxs
  have hyDrop := polyTimeComputable_tail.comp hys
  have heq := funext collisionOutputStep_eq
  exact heq.symm ▸ hc.pairEncode (hxDrop.pairEncode (hyDrop.pairEncode (hout.append hblock)))

/-- Emit one signed difference per declared column using the existing counted-loop
host, with fixed polynomial column and magnitude-width schedules. -/
def collisionOutputPoly (M B : PolyExpr) (z : List Bool) : List Bool :=
  let u := pairFstD z
  let raw := pairSndD z
  let m := M.eval u.length
  let c := List.replicate (B.eval u.length) false
  let init := pairEncode c (pairEncode (raw.take m) (pairEncode (raw.drop m) []))
  let done := pairSndD (BinArith.forLoop collisionOutputStep
    (pairEncode (List.replicate m true) init))
  pairSndD (pairSndD (pairSndD done))

/-- The complete wrapper splits the raw prefix, initializes no output, and runs `m` steps. -/
theorem collisionOutputPoly_eq (M B : PolyExpr) (z : List Bool) :
    collisionOutputPoly M B z =
      let u := pairFstD z
      let raw := pairSndD z
      let m := M.eval u.length
      let c := List.replicate (B.eval u.length) false
      let init := pairEncode c (pairEncode (raw.take m) (pairEncode (raw.drop m) []))
      let done := pairSndD (BinArith.forLoop collisionOutputStep
        (pairEncode (List.replicate m true) init))
      pairSndD (pairSndD (pairSndD done)) := rfl

/-- Every raw input gives exactly one sign and the declared magnitude bits per column.

**Proof sketch.** Each iteration appends exactly width plus one bits, starting from
an empty output. The counted loop executes exactly the declared number of rounds. -/
theorem collisionOutputPoly_length (M B : PolyExpr) (z : List Bool) :
    (collisionOutputPoly M B z).length =
      M.eval (pairFstD z).length * (B.eval (pairFstD z).length + 1) := by
  let u := pairFstD z
  let raw := pairSndD z
  let m := M.eval u.length
  let c := List.replicate (B.eval u.length) false
  let init := pairEncode c (pairEncode (raw.take m) (pairEncode (raw.drop m) []))
  have h (k : ℕ) :
      pairFstD ((collisionOutputStep^[k]) init) = c ∧
      (pairSndD (pairSndD (pairSndD ((collisionOutputStep^[k]) init)))).length =
        k * (c.length + 1) := by
    induction k with
    | zero => simp [init]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨(collisionOutputStep_fst _).trans ih.1, ?_⟩
      simp only [collisionOutputStep_eq, pairSndD_pairEncode, List.length_append,
        List.length_cons, normalizeWidthPoly_length, pairFstD_pairEncode, PolyExpr.eval_var,
        ih.1, ih.2, Nat.succ_mul]
  simp only [collisionOutputPoly_eq, BinArith.forLoop_pairEncode, List.length_replicate,
    pairSndD_pairEncode]
  simpa only [m, u, c, List.length_replicate] using (h m).2

/-- The output is exactly the existing signed encoding of the actual padded/split
integer difference, including at magnitude width zero.

**Proof sketch.** Use the public pad/split readings to identify each raw default bit.
The four Boolean cases give integer differences zero, minus one, one, zero, with the
same sign and truncated magnitude as `SIS.encodeSolution`. Induct over the host counter. -/
theorem collisionOutputPoly_pairEncode (P : TCSlib.Cryptography.SIS.Parameters)
    (M B : PolyExpr) (u raw : List Bool) (hcolumns : P.columns = M.eval u.length) :
    collisionOutputPoly M B (pairEncode u raw) =
      TCSlib.Cryptography.SIS.encodeSolution P (B.eval u.length)
        (collisionDifference P (rawCollisionInputs P.columns raw).1
          (rawCollisionInputs P.columns raw).2) := by
  let width := B.eval u.length
  let c := List.replicate width false
  let m := P.columns
  let block (x y : Bool) :=
    (!x && y) :: Candidates.natToList width (Bool.xor x y).toNat
  have hmag (bit : Bool) :
      normalizeWidthPoly .var (pairEncode c [bit]) = Candidates.natToList width bit.toNat := by
    have hvalue : NumberTheory.listToNat [bit] = bit.toNat := by
      cases bit <;> simp [NumberTheory.listToNat_cons, NumberTheory.listToNat_nil]
    rw [normalizeWidthPoly_pairEncode, hvalue, PolyExpr.eval_var, List.length_replicate]
  have walk (k : ℕ) (xs ys out : List Bool) :
      (collisionOutputStep^[k]) (pairEncode c (pairEncode xs (pairEncode ys out))) =
        pairEncode c (pairEncode (xs.drop k) (pairEncode (ys.drop k)
          (out ++ (List.ofFn fun i : Fin k =>
            block ((xs.drop i.val).headD false) ((ys.drop i.val).headD false)).flatten))) := by
    induction k generalizing xs ys out with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply, collisionOutputStep_eq]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, hmag, ih, List.ofFn_succ,
        List.flatten_cons, Fin.val_zero, Fin.val_succ, List.drop_zero, List.drop_drop,
        Nat.add_comm 1, List.append_assoc, block]
  let padded := (raw ++ List.replicate (m + m) false).take (m + m)
  have hleft : List.ofFn (rawCollisionInputs m raw).1 = padded.take m := by
    rw [rawCollisionInputs_eq, ofFn_splitCoins_fst, ofFn_padFin_eq_take]
  have hright : List.ofFn (rawCollisionInputs m raw).2 = padded.drop m := by
    rw [rawCollisionInputs_eq, ofFn_splitCoins_snd, ofFn_padFin_eq_take]
  have hread (j : ℕ) (hj : j < m + m) : (padded[j]?).getD false = (raw[j]?).getD false := by
    dsimp only [padded]
    rw [List.getElem?_take_of_lt hj]
    by_cases h : j < raw.length
    · rw [List.getElem?_append_left h]
    · have hge := Nat.le_of_not_lt h
      rw [List.getElem?_append_right hge, List.getElem?_eq_none_iff.mpr hge,
        List.getElem?_replicate]
      split <;> rfl
  have hhead (word : List Bool) (j : ℕ) :
      (word.drop j).headD false = (word[j]?).getD false := by
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero]
  have hbits (i : Fin m) :
      ((raw.take m).drop i.val).headD false = (rawCollisionInputs m raw).1 i ∧
      ((raw.drop m).drop i.val).headD false = (rawCollisionInputs m raw).2 i := by
    constructor
    · have h := congrArg (fun w : List Bool => (w[i.val]?).getD false) hleft
      simp only [List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some,
        List.getElem?_take_of_lt i.isLt, hread i.val (by omega)] at h
      rw [hhead, List.getElem?_take_of_lt i.isLt, ← h]
    · have h := congrArg (fun w : List Bool => (w[i.val]?).getD false) hright
      simp only [List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some, List.getElem?_drop,
        hread (m + i.val) (Nat.add_lt_add_left i.isLt m)] at h
      rw [hhead, List.getElem?_drop, ← h]
  have hsign (x y : Bool) : block x y = decide ((x.toNat : ℤ) - y.toNat < 0) ::
      Candidates.natToList width ((x.toNat : ℤ) - y.toNat).natAbs := by
    cases x <;> cases y <;> rfl
  simp only [collisionOutputPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    BinArith.forLoop_pairEncode, List.length_replicate, ← hcolumns]
  change pairSndD (pairSndD (pairSndD ((collisionOutputStep^[m])
    (pairEncode c (pairEncode (raw.take m) (pairEncode (raw.drop m) [])))))) = _
  rw [walk]
  simp only [pairSndD_pairEncode, List.nil_append, TCSlib.Cryptography.SIS.encodeSolution_eq]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  rw [(hbits i).1, (hbits i).2, hsign, collisionDifference_apply]

/-- With a positive magnitude width, parsing recovers the exact integer difference.

**Proof sketch.** Apply the preceding encoder equality and the existing signed
decoder round trip. Each coordinate has absolute value at most one, fitting any
positive width. No canonical finder output length is assumed. -/
theorem decode_collisionOutputPoly (P : TCSlib.Cryptography.SIS.Parameters)
    (M B : PolyExpr) (u raw : List Bool) (hcolumns : P.columns = M.eval u.length)
    (hB : 0 < B.eval u.length) :
    TCSlib.Cryptography.SIS.decodeSolution P (B.eval u.length)
      (collisionOutputPoly M B (pairEncode u raw)) =
      some (collisionDifference P (rawCollisionInputs P.columns raw).1
        (rawCollisionInputs P.columns raw).2) := by
  rw [collisionOutputPoly_pairEncode P M B u raw hcolumns]
  apply TCSlib.Cryptography.SIS.decodeSolution_encodeSolution
  intro i
  have h : (collisionDifference P (rawCollisionInputs P.columns raw).1
      (rawCollisionInputs P.columns raw).2 i).natAbs ≤ 1 := by
    rw [collisionDifference_apply]
    cases (rawCollisionInputs P.columns raw).1 i <;>
      cases (rawCollisionInputs P.columns raw).2 i <;> decide
  exact h.trans_lt (Nat.one_lt_two_pow hB.ne')

/-- The whole fixed-schedule signed-output postprocessor is polynomial-time.

**Proof sketch.** Apply the existing `forLoop_bound_of_ctx 8` and its polynomial-time
contract to the retained-context step. Generate the fixed polynomial templates,
cut the two raw suffixes with `pairTakePoly M` and `pairDropPoly M`, and project the result. -/
theorem polyTimeComputable_collisionOutputPoly (M B : PolyExpr) :
    PolyTimeComputable (collisionOutputPoly M B) := by
  have hloop := BinArith.polyTimeComputable_forLoop polyTimeComputable_collisionOutputStep 9 2
    (BinArith.forLoop_bound_of_ctx 8 collisionOutputStep_fst collisionOutputStep_length_le)
  have hu := polyTimeComputable_pairFstD
  have hc := EnsembleLemmas.polyTimeComputable_zeros B hu
  have hm := (polyTimeComputable_unaryPoly M).comp hu
  have hxs := polyTimeComputable_pairTakePoly M
  have hys := polyTimeComputable_pairDropPoly M
  have hinit := hc.pairEncode (hxs.pairEncode (hys.pairEncode (polyTimeComputable_const [])))
  have hcomposed := (polyTimeComputable_pairSndD.comp BinArith.polyTimeComputable_slot4).comp
    (hloop.comp (hm.pairEncode hinit))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [collisionOutputPoly_eq, Function.comp_apply]

/-- Arbitrary raw collision outputs have success probability at most that of their
actual parsed signed SIS output [Pei16, observations after Equation (4.1.1)].

**Proof sketch.** Use the same matrix/finder coins on both sides. The exact decoder
equation identifies the output with the old integer-difference solver for every raw
word. Apply the existing collision-to-SIS probability bound with the column norm budget. -/
theorem rawCollisionProbability_le_successProbability {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (P : TCSlib.Cryptography.SIS.Parameters) (M B : PolyExpr) (u : List Bool)
    (find : Matrix (Fin P.dimension) (Fin P.columns) (ZMod P.modulus) → ρ → List Bool)
    (hcolumns : P.columns = M.eval u.length) (hB : 0 < B.eval u.length)
    (hbound : P.columns ≤ P.sqNormBound) :
    collisionProbability P (fun A r => rawCollisionInputs P.columns (find A r)) ≤
      TCSlib.Cryptography.SIS.successProbability P
        (fun A r => TCSlib.Cryptography.SIS.decodeSolution P (B.eval u.length)
          (collisionOutputPoly M B (pairEncode u (find A r)))) := by
  have hdecode (raw : List Bool) := decode_collisionOutputPoly P M B u raw hcolumns hB
  simp only [hdecode]
  exact collisionProbability_le_successProbability P _ hbound

end TCSlib.Cryptography.Hashing.SIS
