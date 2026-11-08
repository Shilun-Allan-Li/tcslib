/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Hashing.SIS.Experiments
import TCSlib.Cryptography.SIS.Encoding
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Complexity.ClassP.BinaryArith.Loops

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
Polynomial-time contracts reuse the existing counted-loop host. Nontrivial proofs
remain admitted for the combined statement audit.

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
  sorry

/-- One signed-output step grows linearly in the retained magnitude width.

**Proof sketch.** Both bit suffixes shrink and the output appends one sign plus
exactly the retained number of magnitude bits. Public pairing lengths cover malformed
framing with the stated constant slack. -/
theorem collisionOutputStep_length_le (z : List Bool) :
    (collisionOutputStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  sorry

/-- The signed-output leaf step is polynomial-time.

**Proof sketch.** Compose the public head/default, Boolean not/and/xor, cons,
append, drop and pairing machines with `normalizeWidthPoly .var`. These are leaf
operations; no signed arithmetic, hash evaluation or collision test is performed. -/
theorem polyTimeComputable_collisionOutputStep : PolyTimeComputable collisionOutputStep := by
  sorry

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
  sorry

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
  sorry

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
  sorry

/-- The whole fixed-schedule signed-output postprocessor is polynomial-time.

**Proof sketch.** Apply the existing `forLoop_bound_of_ctx 8` and its polynomial-time
contract to the retained-context step. Generate the fixed polynomial templates,
cut the two raw suffixes with `pairTakePoly M` and `pairDropPoly M`, and project the result. -/
theorem polyTimeComputable_collisionOutputPoly (M B : PolyExpr) :
    PolyTimeComputable (collisionOutputPoly M B) := by
  sorry

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
  sorry

end TCSlib.Cryptography.Hashing.SIS
