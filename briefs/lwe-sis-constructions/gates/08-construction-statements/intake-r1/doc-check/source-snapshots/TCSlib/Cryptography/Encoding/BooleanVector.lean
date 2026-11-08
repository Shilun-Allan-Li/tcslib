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
uses existing leaf contracts and the existing public counted loop. The loop's
registry disposition remains pending; dependent FP fills are paused. Nontrivial
claims are admitted.

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
  sorry

/-- The expansion step grows by a linear function of the width context.

**Proof sketch.** The raw bit suffix shrinks and the output gains exactly the
retained width. Public pairing lengths cover malformed inner framing with slack eight. -/
theorem expandStep_length_le (z : List Bool) :
    (expandStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  sorry

/-- The bit-expansion step is polynomial-time.

**Proof sketch.** Compose public total projections, head/default singleton, drop,
append and pairing contracts with `normalizeWidthPoly .var`. -/
theorem polyTimeComputable_expandStep : PolyTimeComputable expandStep := by
  sorry

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
  sorry

/-- Expansion agrees with the canonical modular vector of the actual raw padded prefix.

**Proof sketch.** Induct over the counted bits. Each head/default is the corresponding
coordinate of `padFin`; the four numeral/width-zero cases match the existing fixed-width
encoder. Read the public pad/word correspondence when filling this proof. -/
theorem expandPoly_encode {q : ℕ} [NeZero q] (M W : PolyExpr) (u raw : List Bool)
    (hq : q = 2 ^ (W.eval u.length)) :
    expandPoly M W (pairEncode u raw) = Modular.encodeVector (W.eval u.length)
      (fun i : Fin (M.eval u.length) => ((padFin (M.eval u.length) raw i).toNat : ZMod q)) := by
  sorry

/-- Every fixed polynomial bit-expansion schedule is polynomial-time.

**Proof sketch.** Use the retained-context envelope with `forLoop_bound_of_ctx 8`
and `polyTimeComputable_forLoop`, generate templates with existing zero/unary polynomial
machines, and compose total projections. No new host or runtime polynomial is needed. -/
theorem polyTimeComputable_expandPoly (M W : PolyExpr) : PolyTimeComputable (expandPoly M W) := by
  sorry

end TCSlib.Cryptography.Encoding.BooleanVector
