/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Complexity.ClassP.BinaryArith.Loops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Binary domain words as encoded modular vectors

## Main definitions

* `expandStep`: append a fixed-width numeral for the next raw bit, defaulting false.
* `expandPoly`: run the existing counted loop at fixed polynomial count and width.

## Main results

The raw output length is exact. Its values are the modular zero/one vector of the
original prefix, with false defaults and excess bits ignored. The efficiency sketch
uses existing leaf contracts and the public counted loop. The step is polynomial-time.
The wrapper composes the registered counted loop with the schedule templates and projections.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Equation (4.1.1) (the binary hash domain).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Section 2.1 (binary representations and machine tapes).

This is representation glue, with no new sampler, hardness assumption or generic
block-traversal host. The polynomial schedules are fixed before the machine is chosen.
-/

namespace TCSlib.Cryptography.Encoding.BooleanVector

open Complexity Turing
open BinaryArith

/-- Consume one bit with a false default and append its normalized full-width numeral. -/
def expandStep (z : List Bool) : List Bool :=
  let c := pairFstD z
  let bits := pairFstD (pairSndD z)
  let out := pairSndD (pairSndD z)
  pairEncode c (pairEncode (bits.drop 1)
    (out ++ normalizeWidthPoly .var (pairEncode c [bits.headD false])))

/-- The complete expansion step appends precisely the normalized numeral of the next bit. -/
theorem expandStep_eq (z : List Bool) :
    expandStep z =
      let c := pairFstD z
      let bits := pairFstD (pairSndD z)
      let out := pairSndD (pairSndD z)
      pairEncode c (pairEncode (bits.drop 1)
        (out ++ normalizeWidthPoly .var (pairEncode c [bits.headD false]))) := rfl

/-- The expansion step preserves the full width context.

**Proof sketch.** Read the step equation and the public pair-first equation. -/
theorem expandStep_fst (z : List Bool) : pairFstD (expandStep z) = pairFstD z := by
  rw [expandStep_eq, pairFstD_pairEncode]

/-- The expansion step grows by a linear function of the width context.

**Proof sketch.** The raw bit suffix shrinks and the output gains exactly the
retained width. Public pairing lengths cover malformed inner framing with slack eight. -/
theorem expandStep_length_le (z : List Bool) :
    (expandStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  have houter := length_pair_components_le z
  have hinner := length_pair_components_le (pairSndD z)
  simp only [expandStep_eq, length_pairEncode, List.length_drop, List.length_append,
    normalizeWidthPoly_length, pairFstD_pairEncode, PolyExpr.eval_var]
  omega

/-- The bit-expansion step is polynomial-time.

**Proof sketch.** Compose public total projections, head/default singleton, drop,
append and pairing contracts with `normalizeWidthPoly .var`. -/
theorem polyTimeComputable_expandStep : PolyTimeComputable expandStep := by
  have hc := polyTimeComputable_pairFstD
  have hbits := BinArith.polyTimeComputable_slot2
  have hout := BinArith.polyTimeComputable_slot3
  have hnext := (polyTimeComputable_normalizeWidthPoly .var).comp
    (hc.pairEncode (polyTimeComputable_headD.comp hbits))
  have hdrop := polyTimeComputable_tail.comp hbits
  have heq := funext expandStep_eq
  exact heq.symm ▸ hc.pairEncode (hdrop.pairEncode (hout.append hnext))

/-- Write one modular residue per declared raw prefix bit, using fixed polynomial
count and width schedules and the original public counted-loop host. -/
def expandPoly (M W : PolyExpr) (z : List Bool) : List Bool :=
  let u := pairFstD z
  let c := List.replicate (W.eval u.length) false
  let init := pairEncode c (pairEncode (pairSndD z) [])
  let done := pairSndD (BinArith.forLoop expandStep
    (pairEncode (List.replicate (M.eval u.length) true) init))
  pairSndD (pairSndD done)

/-- The complete wrapper starts with empty output and executes the declared bit count. -/
theorem expandPoly_eq (M W : PolyExpr) (z : List Bool) :
    expandPoly M W z =
      let u := pairFstD z
      let c := List.replicate (W.eval u.length) false
      let init := pairEncode c (pairEncode (pairSndD z) [])
      let done := pairSndD (BinArith.forLoop expandStep
        (pairEncode (List.replicate (M.eval u.length) true) init))
      pairSndD (pairSndD done) := rfl

/-- Expansion writes exactly count times width bits on arbitrary raw inputs.

**Proof sketch.** Each loop round appends exactly the width and the initial output
is empty. The finite counter terminates even when count or width is zero. -/
theorem expandPoly_length (M W : PolyExpr) (z : List Bool) :
    (expandPoly M W z).length = M.eval (pairFstD z).length * W.eval (pairFstD z).length := by
  let c := List.replicate (W.eval (pairFstD z).length) false
  let init := pairEncode c (pairEncode (pairSndD z) [])
  have h (k : ℕ) :
      pairFstD ((expandStep^[k]) init) = c ∧
      (pairSndD (pairSndD ((expandStep^[k]) init))).length = k * c.length := by
    induction k with
    | zero => simp [init]
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨(expandStep_fst _).trans ih.1, ?_⟩
      simp only [expandStep_eq, pairSndD_pairEncode, List.length_append,
        normalizeWidthPoly_length, pairFstD_pairEncode, PolyExpr.eval_var, ih.1, ih.2,
        Nat.succ_mul]
  simp only [expandPoly_eq, BinArith.forLoop_pairEncode, List.length_replicate, pairSndD_pairEncode]
  simpa only [c, List.length_replicate] using (h (M.eval (pairFstD z).length)).2

/-- Expansion agrees with the canonical modular vector of the actual raw padded prefix.

**Proof sketch.** Induct over the counted bits, recording the emitted blocks at
successive raw head/default positions. The public padded-word equation identifies
those bits with `padFin`. The residue reader and the numeral's modular invariance
also give the required block when the width is zero. -/
theorem expandPoly_encode {q : ℕ} [NeZero q] (M W : PolyExpr) (u raw : List Bool)
    (hq : q = 2 ^ (W.eval u.length)) :
    expandPoly M W (pairEncode u raw) = Modular.encodeVector (W.eval u.length)
      (fun i : Fin (M.eval u.length) => ((padFin (M.eval u.length) raw i).toNat : ZMod q)) := by
  let width := W.eval u.length
  let c := List.replicate width false
  let block (bit : Bool) := Candidates.natToList width ((bit.toNat : ZMod q).val)
  have hblock (bit : Bool) : normalizeWidthPoly .var (pairEncode c [bit]) = block bit := by
    have hvalue : NumberTheory.listToNat [bit] = bit.toNat := by
      cases bit <;> simp [NumberTheory.listToNat_cons, NumberTheory.listToNat_nil]
    rw [normalizeWidthPoly_pairEncode, hvalue, PolyExpr.eval_var, List.length_replicate]
    dsimp only [block]
    rw [ZMod.val_natCast, hq, Candidates.natToList_mod_two_pow]
  have walk (k : ℕ) (word out : List Bool) :
      (expandStep^[k]) (pairEncode c (pairEncode word out)) =
        pairEncode c (pairEncode (word.drop k)
          (out ++ (List.ofFn fun i : Fin k => block ((word.drop i.val).headD false)).flatten)) := by
    induction k generalizing word out with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply, expandStep_eq]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, hblock, ih, List.ofFn_succ,
        List.flatten_cons, Fin.val_zero, Fin.val_succ, List.drop_zero, List.drop_drop,
        Nat.add_comm 1, List.append_assoc]
  have hbit (i : Fin (M.eval u.length)) : (raw.drop i.val).headD false =
      padFin (M.eval u.length) raw i := by
    have h := congrArg (fun w : List Bool => (w[i.val]?).getD false)
      (ofFn_padFin_eq_take (M.eval u.length) raw)
    simp only [List.getElem?_ofFn, dif_pos i.isLt, Option.getD_some,
      List.getElem?_take_of_lt i.isLt] at h
    rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero, h]
    by_cases hi : i.val < raw.length
    · rw [List.getElem?_append_left hi]
    · rw [List.getElem?_eq_none_iff.mpr (Nat.le_of_not_lt hi),
        List.getElem?_append_right (Nat.le_of_not_lt hi), List.getElem?_replicate]
      split <;> rfl
  simp only [expandPoly_eq, pairFstD_pairEncode, pairSndD_pairEncode, BinArith.forLoop_pairEncode,
    List.length_replicate]
  change pairSndD (pairSndD ((expandStep^[M.eval u.length]) (pairEncode c (pairEncode raw [])))) = _
  rw [walk]
  simp only [pairSndD_pairEncode, List.nil_append, hbit, block, width, Modular.encodeVector_eq]

/-- Every fixed polynomial bit-expansion schedule is polynomial-time.

**Proof sketch.** Use the retained-context envelope with `forLoop_bound_of_ctx 8`
and `polyTimeComputable_forLoop`, generate templates with existing zero/unary polynomial
machines, and compose total projections. No new host or runtime polynomial is needed. -/
theorem polyTimeComputable_expandPoly (M W : PolyExpr) : PolyTimeComputable (expandPoly M W) := by
  have hloop := BinArith.polyTimeComputable_forLoop polyTimeComputable_expandStep 9 2
    (BinArith.forLoop_bound_of_ctx 8 expandStep_fst expandStep_length_le)
  have hu := polyTimeComputable_pairFstD
  have hc := EnsembleLemmas.polyTimeComputable_zeros W hu
  have hm := (polyTimeComputable_unaryPoly M).comp hu
  have hinit := hc.pairEncode
    (polyTimeComputable_pairSndD.pairEncode (polyTimeComputable_const []))
  have hcomposed := BinArith.polyTimeComputable_slot4.comp
    (hloop.comp (hm.pairEncode hinit))
  refine Eq.mp (congrArg PolyTimeComputable ?_) hcomposed
  funext z
  simp only [expandPoly_eq, Function.comp_apply]

end TCSlib.Cryptography.Encoding.BooleanVector
