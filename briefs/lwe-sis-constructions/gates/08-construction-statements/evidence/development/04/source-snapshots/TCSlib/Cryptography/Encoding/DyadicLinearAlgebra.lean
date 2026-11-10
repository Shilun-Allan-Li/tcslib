/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encoding.DyadicArithmetic
import TCSlib.Cryptography.Encoding.Modular
import TCSlib.Complexity.ClassP.BinaryArith.Loops

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Encoded dyadic dot products and matrix-vector multiplication

## Main definitions

* `dotStep`, `dotWords`, `dotPoly`: consume fixed-width blocks in the existing counted loop.
* `matVecStep`, `matVecPoly`: consume row-major matrix rows with that same public host.

## Main results

Raw output widths are unconditional. Canonical encodings correspond to modular dot
products and matrix-vector multiplication. Explicit state-growth bounds support the
polynomial-time statements. Nontrivial proofs remain admitted for the combined audit.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, 3rd ed., January 2010,
  Section 2.1 (machine representations).
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, 2009,
  Section 7.2 (polynomial-time randomized computation, model context).
* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, 17 February 2016,
  Definitions 4.1.1 and 4.2.3 (the modular products being represented).

These algorithms are repository adaptations assembled from scalar arithmetic and
`Complexity.BinArith.forLoop`; no new traversal host is defined. Counters and retained
width words have explicit polynomial lengths. Short raw final blocks are read as their
ordinary MSB numeral, hence with implicit leading zeros; this is not a claim that the
flat operand is padded at its end. Malformed pairs use the existing total projections.
-/

namespace TCSlib.Cryptography.Encoding.DyadicLinearAlgebra

open Complexity
open DyadicArithmetic

/-- Consume one coordinate pair and update the modular accumulator, retaining the
width word. This is the leaf step for the public counted-loop dot product. -/
def dotStep (z : List Bool) : List Bool :=
  let c := pairFstD z
  let xs := pairFstD (pairSndD z)
  let ys := pairFstD (pairSndD (pairSndD z))
  let acc := pairSndD (pairSndD (pairSndD z))
  pairEncode c (pairEncode (xs.drop c.length)
    (pairEncode (ys.drop c.length)
      (addPoly .var (pairEncode c (pairEncode acc
        (mulPoly .var (pairEncode c
          (pairEncode (xs.take c.length) (ys.take c.length)))))))))

/-- The complete step drops one width block per operand and adds their modular product. -/
theorem dotStep_eq (z : List Bool) :
    dotStep z =
      let c := pairFstD z
      let xs := pairFstD (pairSndD z)
      let ys := pairFstD (pairSndD (pairSndD z))
      let acc := pairSndD (pairSndD (pairSndD z))
      pairEncode c (pairEncode (xs.drop c.length)
        (pairEncode (ys.drop c.length)
          (addPoly .var (pairEncode c (pairEncode acc
            (mulPoly .var (pairEncode c
              (pairEncode (xs.take c.length) (ys.take c.length))))))))) := rfl

/-- The dot step preserves its entire width context, including on malformed input.

**Proof sketch.** Read the complete step equation and the public pair-first equation. -/
theorem dotStep_fst (z : List Bool) : pairFstD (dotStep z) = pairFstD z := by
  sorry

/-- One dot step grows by at most eight times the width-context size plus one.

**Proof sketch.** The two operands only shrink. Scalar arithmetic writes exactly the
retained width, even on malformed data. Expand public pairing lengths and bound any
framing repair by the stated slack; no numeric operand value enters the bound. -/
theorem dotStep_length_le (z : List Bool) :
    (dotStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  sorry

/-- The dot-product leaf step is polynomial-time, with no runtime polynomial argument.

**Proof sketch.** Compose total projections, take/drop-by-length machines, pairing,
and the already proved scalar `addPoly .var` and `mulPoly .var` contracts. The width
template is the retained word itself, so the per-step output bound is linear in it. -/
theorem polyTimeComputable_dotStep : PolyTimeComputable dotStep := by
  sorry

/-- Run one dot step per letter of `n`, starting with a zero accumulator of width `|c|`.
Only the lengths of the two template words are used. -/
def dotWords (c n x y : List Bool) : List Bool :=
  let init := pairEncode c (pairEncode x (pairEncode y (List.replicate c.length false)))
  let done := pairSndD (BinArith.forLoop dotStep (pairEncode n init))
  pairSndD (pairSndD (pairSndD done))

/-- The complete dot loop initializes width-many zeros and extracts the final accumulator. -/
theorem dotWords_eq (c n x y : List Bool) :
    dotWords c n x y =
      let init := pairEncode c (pairEncode x (pairEncode y (List.replicate c.length false)))
      let done := pairSndD (BinArith.forLoop dotStep (pairEncode n init))
      pairSndD (pairSndD (pairSndD done)) := rfl

/-- The dot loop always writes exactly the width word's length.

**Proof sketch.** At zero iterations the initialized accumulator has that length.
Each later step replaces it with the fixed-width scalar sum. Use the public counted
loop equation, including when the count or width is zero. -/
theorem dotWords_length (c n x y : List Bool) : (dotWords c n x y).length = c.length := by
  sorry

/-- The packed four-argument dot loop is polynomial-time on all raw words.

**Proof sketch.** Apply `forLoop_bound_of_ctx 8` to the retained-context and growth
lemmas, then `polyTimeComputable_forLoop` with envelope constants nine and two.
Initialize zeros and compose the final projections with the existing FP calculus. -/
theorem polyTimeComputable_dotWords : PolyTimeComputable
    (fun z => dotWords (pairFstD z) (pairFstD (pairSndD z))
      (pairFstD (pairSndD (pairSndD z))) (pairSndD (pairSndD (pairSndD z)))) := by
  sorry

/-- Fix polynomial coordinate and residue-width schedules before selecting a dot machine. -/
def dotPoly (N W : PolyExpr) (z : List Bool) : List Bool :=
  dotWords (List.replicate (W.eval (pairFstD z).length) false)
    (List.replicate (N.eval (pairFstD z).length) true)
    (pairFstD (pairSndD z)) (pairSndD (pairSndD z))

/-- The complete wrapper derives both loop templates from the parameter word's length. -/
theorem dotPoly_eq (N W : PolyExpr) (z : List Bool) :
    dotPoly N W z =
      dotWords (List.replicate (W.eval (pairFstD z).length) false)
        (List.replicate (N.eval (pairFstD z).length) true)
        (pairFstD (pairSndD z)) (pairSndD (pairSndD z)) := rfl

/-- The polynomial dot wrapper has its declared width on every raw input.

**Proof sketch.** Apply `dotWords_length` and the public replicate-length equation. -/
theorem dotPoly_length (N W : PolyExpr) (z : List Bool) :
    (dotPoly N W z).length = W.eval (pairFstD z).length := by
  sorry

/-- On canonical full-width vectors the loop writes their modular inner product
[Pei16, Definitions 4.1.1 and 4.2.3, representation correspondence].

**Proof sketch.** Induct over the counted coordinates. Public vector slicing reads
the next canonical blocks; scalar multiplication and addition preserve the running
sum in `ZMod q`. At termination the accumulator is the canonical fixed-width numeral. -/
theorem dotPoly_encodeVector {q : ℕ} [NeZero q] (N W : PolyExpr) (u : List Bool)
    (hq : q = 2 ^ (W.eval u.length))
    (a b : Fin (N.eval u.length) → ZMod q) :
    dotPoly N W (pairEncode u
      (pairEncode (Modular.encodeVector (W.eval u.length) a)
        (Modular.encodeVector (W.eval u.length) b))) =
      Candidates.natToList (W.eval u.length) (∑ i, a i * b i).val := by
  sorry

/-- Every fixed polynomial dot schedule has a polynomial-time implementation.

**Proof sketch.** Generate the two unary templates with the existing polynomial
zero-word machine (and its true-word analogue by complement), then compose the
packed `dotWords` machine. The polynomials are fixed outside the machine choice. -/
theorem polyTimeComputable_dotPoly (N W : PolyExpr) : PolyTimeComputable (dotPoly N W) := by
  sorry

/-- Consume one matrix row, append its modular dot product, and retain width, column
count and the full input vector as the outer loop's context. -/
def matVecStep (z : List Bool) : List Bool :=
  let ctx := pairFstD z
  let c := pairFstD ctx
  let n := pairFstD (pairSndD ctx)
  let v := pairSndD (pairSndD ctx)
  let rows := pairFstD (pairSndD z)
  let out := pairSndD (pairSndD z)
  let rowWidth := n.length * c.length
  pairEncode ctx (pairEncode (rows.drop rowWidth)
    (out ++ dotWords c n (rows.take rowWidth) v))

/-- The complete row step uses a row of `|n|*|c|` bits and appends one width-sized result. -/
theorem matVecStep_eq (z : List Bool) :
    matVecStep z =
      let ctx := pairFstD z
      let c := pairFstD ctx
      let n := pairFstD (pairSndD ctx)
      let v := pairSndD (pairSndD ctx)
      let rows := pairFstD (pairSndD z)
      let out := pairSndD (pairSndD z)
      let rowWidth := n.length * c.length
      pairEncode ctx (pairEncode (rows.drop rowWidth)
        (out ++ dotWords c n (rows.take rowWidth) v)) := rfl

/-- The outer row step preserves its entire vector-and-dimension context.

**Proof sketch.** Read the step equation and the public pair-first equation. -/
theorem matVecStep_fst (z : List Bool) : pairFstD (matVecStep z) = pairFstD z := by
  sorry

/-- One row step has linear growth in its retained context size.

**Proof sketch.** The matrix suffix only shrinks and the output grows by exactly
the width, using `dotWords_length`. Public pairing lengths cover malformed framing
with the stated constant slack. -/
theorem matVecStep_length_le (z : List Bool) :
    (matVecStep z).length ≤ z.length + 8 * ((pairFstD z).length + 1) := by
  sorry

/-- The matrix row step is polynomial-time using the already registered loop host.

**Proof sketch.** Obtain the row-cut template with the public unary multiplication
machine `BinArith.mulU`, whose length is `|n|*|c|`. Compose take/drop-by-length,
the packed dot loop, append and total projections. No matrix traversal is rebuilt. -/
theorem polyTimeComputable_matVecStep : PolyTimeComputable matVecStep := by
  sorry

/-- Multiply a row-major matrix by a vector using fixed polynomial row, column and
residue-width schedules and the existing counted-loop host. -/
def matVecPoly (M N W : PolyExpr) (z : List Bool) : List Bool :=
  let u := pairFstD z
  let c := List.replicate (W.eval u.length) false
  let n := List.replicate (N.eval u.length) true
  let ctx := pairEncode c (pairEncode n (pairSndD (pairSndD z)))
  let init := pairEncode ctx (pairEncode (pairFstD (pairSndD z)) [])
  let done := pairSndD (BinArith.forLoop matVecStep
    (pairEncode (List.replicate (M.eval u.length) true) init))
  pairSndD (pairSndD done)

/-- The complete wrapper initializes an empty output and runs one step per declared row. -/
theorem matVecPoly_eq (M N W : PolyExpr) (z : List Bool) :
    matVecPoly M N W z =
      let u := pairFstD z
      let c := List.replicate (W.eval u.length) false
      let n := List.replicate (N.eval u.length) true
      let ctx := pairEncode c (pairEncode n (pairSndD (pairSndD z)))
      let init := pairEncode ctx (pairEncode (pairFstD (pairSndD z)) [])
      let done := pairSndD (BinArith.forLoop matVecStep
        (pairEncode (List.replicate (M.eval u.length) true) init))
      pairSndD (pairSndD done) := rfl

/-- The matrix wrapper writes exactly row-count times width bits on every raw input.

**Proof sketch.** The initialized output is empty and each counted row appends exactly
the retained width by `dotWords_length`. No positive width or column count is needed. -/
theorem matVecPoly_length (M N W : PolyExpr) (z : List Bool) :
    (matVecPoly M N W z).length =
      M.eval (pairFstD z).length * W.eval (pairFstD z).length := by
  sorry

/-- On canonical inputs the matrix loop writes the existing modular matrix-vector product
[Pei16, Definition 4.2.3, representation correspondence].

**Proof sketch.** Induct over the outer counted rows and apply `dotPoly`'s inner-loop
invariant to each exact row. Concatenating the fixed-width results is precisely the
public vector encoder. Empty rows, columns and width are handled by the counters. -/
theorem matVecPoly_encodeMatrix {q : ℕ} [NeZero q] (M N W : PolyExpr) (u : List Bool)
    (hq : q = 2 ^ (W.eval u.length))
    (A : Matrix (Fin (M.eval u.length)) (Fin (N.eval u.length)) (ZMod q))
    (v : Fin (N.eval u.length) → ZMod q) :
    matVecPoly M N W (pairEncode u
      (pairEncode (Modular.encodeMatrix (W.eval u.length) A)
        (Modular.encodeVector (W.eval u.length) v))) =
      Modular.encodeVector (W.eval u.length) (A.mulVec v) := by
  sorry

/-- Every fixed polynomial matrix-vector schedule has a polynomial-time implementation.

**Proof sketch.** Apply the public retained-context loop envelope with constant eight
to `matVecStep`, obtaining the nine/two polynomial bound. Generate the fixed schedule
templates with existing polynomial unary-word machines and compose final projections. -/
theorem polyTimeComputable_matVecPoly (M N W : PolyExpr) :
    PolyTimeComputable (matVecPoly M N W) := by
  sorry

end TCSlib.Cryptography.Encoding.DyadicLinearAlgebra
