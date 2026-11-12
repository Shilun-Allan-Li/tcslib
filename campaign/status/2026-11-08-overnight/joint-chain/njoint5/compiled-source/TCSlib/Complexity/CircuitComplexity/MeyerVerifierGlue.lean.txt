/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.MeyerTableau
import TCSlib.Complexity.CircuitComplexity.KarpLiptonPrefix
import TCSlib.Complexity.CircuitComplexity.CircuitEval
import TCSlib.Complexity.CircuitComplexity.CircuitSatReductionValid
import TCSlib.Complexity.ClassNP.CoNP

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Meyer's theorem: polynomial-time glue for the verifier

The polynomial-time building blocks of the `Σ₂ᵖ` verifier of Meyer's theorem
([AB09, Thm 6.20]): the coordinates of a verifier input
`⟨⟨x, U⟩, ⟨⟨t, a⟩, ⟨j, p⟩⟩⟩`, and the polynomial-time construction of queries to the
guessed circuit (`pt_query`, through the one-pass transducer `fT` turning
`Turing.pairEncode`'s doubled-bit code into the tableau machine's field code).

## Main definitions

* `Complexity.Meyer.vx`, `vD`, `vt`, `va`, `vj`, `vp`, `vin` — coordinates and instances.
* `Complexity.Meyer.wd` — the width `Cw (n+1)^cw`; `TW`, `AW`, `twd`, `awd` — the time and
  offset words of an instance.

## Main results

* `Complexity.Meyer.fT_pairEncode`, `Complexity.Meyer.pt_query` — queries are
  polynomial-time constructible.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.4, Theorem 6.20, pp. 114–115.)
-/

namespace Complexity.Meyer

open Turing Complexity.PolyHierarchy BoolCircuit BoolCircuit.CktSatReduction
  Complexity.KarpLipton Complexity.TimeHierarchy

/-! ### Coordinates of a verifier input -/

/-- The input `x` of a verifier input `⟨⟨x, U⟩, ⟨⟨t, a⟩, ⟨j, p⟩⟩⟩`. -/
def vx (z : List Bool) : List Bool := pairFstD (pairFstD z)
/-- The guessed circuit description: `U` with its padding marker dropped. -/
def vD (z : List Bool) : List Bool := dropMarker (pairSndD (pairFstD z))
/-- The time word. -/
def vt (z : List Bool) : List Bool := pairFstD (pairFstD (pairSndD z))
/-- The offset word. -/
def va (z : List Bool) : List Bool := pairSndD (pairFstD (pairSndD z))
/-- The unary input offset. -/
def vj (z : List Bool) : List Bool := pairFstD (pairSndD (pairSndD z))
/-- The padding word of the binary input offset. -/
def vp (z : List Bool) : List Bool := pairSndD (pairSndD (pairSndD z))

/-- The verifier input of an instance. -/
def vin (x U t a j p : List Bool) : List Bool :=
  pairEncode (pairEncode x U) (pairEncode (pairEncode t a) (pairEncode j p))

section coords
variable (x U t a j p : List Bool)
/-- The input coordinate of an instance. -/
@[simp] theorem vx_vin : vx (vin x U t a j p) = x := by simp [vx, vin]
/-- The description coordinate of an instance is the unpadded description. -/
@[simp] theorem vD_vin : vD (vin x U t a j p) = dropMarker U := by simp [vD, vin]
/-- The time-word coordinate of an instance. -/
@[simp] theorem vt_vin : vt (vin x U t a j p) = t := by simp [vt, vin]
/-- The offset-word coordinate of an instance. -/
@[simp] theorem va_vin : va (vin x U t a j p) = a := by simp [va, vin]
/-- The unary input-offset coordinate of an instance. -/
@[simp] theorem vj_vin : vj (vin x U t a j p) = j := by simp [vj, vin]
/-- The padding coordinate of an instance. -/
@[simp] theorem vp_vin : vp (vin x U t a j p) = p := by simp [vp, vin]
end coords

/-- The input coordinate is polynomial-time computable. -/
theorem pt_vx : PolyTimeComputable vx :=
  polyTimeComputable_pairFstD.comp polyTimeComputable_pairFstD
/-- The description coordinate is polynomial-time computable. -/
theorem pt_vD : PolyTimeComputable vD :=
  polyTimeComputable_dropMarker.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)
/-- The time-word coordinate is polynomial-time computable. -/
theorem pt_vt : PolyTimeComputable vt :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
/-- The offset-word coordinate is polynomial-time computable. -/
theorem pt_va : PolyTimeComputable va :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)
/-- The unary input-offset coordinate is polynomial-time computable. -/
theorem pt_vj : PolyTimeComputable vj :=
  polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
/-- The padding coordinate is polynomial-time computable. -/
theorem pt_vp : PolyTimeComputable vp :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)

/-! ### Polynomial-time word functions -/

/-- Fixed-width increment (overflow to `[]`) is polynomial-time. -/
theorem pt_inc : PolyTimeComputable (fun u => (incFixed u).getD []) := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_incFixed
  exact polyTimeComputable_of_linear ⟨M, c, hM⟩

/-- The binary length code is polynomial-time. -/
theorem pt_lengthBits : PolyTimeComputable (fun u => Nat.bits u.length) := by
  obtain ⟨M, c, hM⟩ := Turing.FinTM.computesFunInTime_lengthBits
  exact polyTimeComputable_of_linear ⟨M, c, hM⟩

/-- The constant-bit map `u ↦ b^|u|` as a transducer. -/
def constMap (b : Bool) (u : List Bool) : List Bool := transduce (fun _ _ => ()) (fun _ _ => some b) () u

/-- The constant-bit transducer maps a word to the constant word of its length. -/
@[simp] theorem constMap_eq (b : Bool) (u : List Bool) : constMap b u = List.replicate u.length b := by
  induction u with
  | nil => rfl
  | cons c u ih => simp [constMap, transduce] at ih ⊢; simp [ih, List.replicate_succ]

/-- The constant-bit transducer is polynomial-time computable. -/
theorem pt_constMap (b : Bool) : PolyTimeComputable (constMap b) :=
  polyTimeComputable_transduce _ _ _

/-- The transducer turning `pairEncode`'s doubled-bit code into the field code: pairs
`(b, b)` become `(b, true)`, the separator `(false, true)` becomes the end pair
`(false, false)`, after which the rest is copied. States: `none` = copying, `some none` =
before a pair, `some (some b)` = after a pair's first symbol `b`. -/
def fTδ : Option (Option Bool) → Bool → Option (Option Bool)
  | none, _ => none
  | some none, b => some (some b)
  | some (some b₁), b₂ => if b₁ = b₂ then some none else none

/-- The emissions of `fTδ`. -/
def fTo : Option (Option Bool) → Bool → Option Bool
  | none, b => some b
  | some none, b => some b
  | some (some b₁), b₂ => some (decide (b₁ = b₂))

/-- The field-code transducer. -/
def fT (u : List Bool) : List Bool := transduce fTδ fTo (some none) u

/-- In copying mode the transducer is the identity. -/
theorem transduce_fT_copy (u : List Bool) : transduce fTδ fTo none u = u := by
  induction u with
  | nil => rfl
  | cons b u ih => simp [transduce, fTδ, fTo, ih]

/-- **The field-code transducer on a pair.** -/
theorem fT_pairEncode (w r : List Bool) : fT (pairEncode w r) = fcode w ++ false :: false :: r := by
  induction w with
  | nil => simp [fT, pairEncode, transduce, fTδ, fTo, transduce_fT_copy, fcode]
  | cons b w ih =>
    simp only [fT, pairEncode, List.flatMap_cons, List.cons_append, List.nil_append,
      List.append_assoc, transduce, fTδ, fTo, decide_true] at ih ⊢
    simp only [if_true, Option.toList, List.cons_append, List.nil_append]
    rw [ih]; rfl

/-- The field-code transducer is polynomial-time computable. -/
theorem pt_fT : PolyTimeComputable fT := polyTimeComputable_transduce _ _ _

/-- **Queries are polynomial-time constructible** from polynomial-time fields. -/
theorem pt_query {nb : ℕ} (bits : Fin nb → Bool) {T A X : List Bool → List Bool}
    (hT : PolyTimeComputable T) (hA : PolyTimeComputable A) (hX : PolyTimeComputable X) :
    PolyTimeComputable (fun z => query bits (T z) (A z) (X z)) := by
  have h : (fun z => query bits (T z) (A z) (X z)) =
      fun z => List.ofFn bits ++ fT (pairEncode (T z) (fT (pairEncode (A z) (X z)))) := by
    funext z; simp [query, fT_pairEncode]
  rw [h]
  exact (polyTimeComputable_prepend _).comp (pt_fT.comp (hT.pairEncode (pt_fT.comp (hA.pairEncode hX))))

/-! ### The words of an instance -/

/-- **The width** `W = Cw (n + 1)^cw` of time and offset words for inputs of length `n`. -/
def wd (Cw cw n : ℕ) : ℕ := Cw * (n + 1) ^ cw

/-- The time words of an instance: the current time `t`, its successor, `0`, and the
last time `2^W - 1`. -/
inductive TW where
  | tc | tn | t0 | t1
  deriving DecidableEq, Fintype

/-- The offset words of an instance: the current offset `a`, its successor, `0`, `1`,
and the binary codes of the unary input offset `j` and of `j + 1`. -/
inductive AW where
  | ac | an | a0 | a1 | aj | aj1
  deriving DecidableEq, Fintype

variable (Cw cw : ℕ)

/-- The binary code of the unary input offset, padded with the padding word. -/
def bjw (z : List Bool) : List Bool :=
  Nat.bits (vj z).length ++ List.replicate (vp z).length false

/-- The time word `T` of a verifier input. -/
def twd : TW → List Bool → List Bool
  | .tc, z => vt z
  | .tn, z => (incFixed (vt z)).getD []
  | .t0, z => List.replicate (wd Cw cw (vx z).length) false
  | .t1, z => List.replicate (wd Cw cw (vx z).length) true

/-- The offset word `A` of a verifier input. -/
def awd : AW → List Bool → List Bool
  | .ac, z => va z
  | .an, z => (incFixed (va z)).getD []
  | .a0, z => List.replicate (wd Cw cw (vx z).length) false
  | .a1, z => (incFixed (List.replicate (wd Cw cw (vx z).length) false)).getD []
  | .aj, z => bjw z
  | .aj1, z => (incFixed (bjw z)).getD []

/-- The constant word of the width `W` is polynomial-time computable from a verifier input. -/
theorem pt_rep (b : Bool) :
    PolyTimeComputable (fun z => List.replicate (wd Cw cw (vx z).length) b) := by
  have h := (pt_constMap b).comp (unaryPT_poly Cw cw pt_vx)
  convert h using 1
  funext z; simp [wd]

/-- The padded binary code of the unary input offset is polynomial-time computable. -/
theorem pt_bjw : PolyTimeComputable bjw := by
  have h := PolyTimeComputable.append (pt_lengthBits.comp pt_vj)
    ((pt_constMap false).comp (polyTimeComputable_unary.comp pt_vp))
  convert h using 1
  funext z; simp [bjw]

/-- Every time word of an instance is polynomial-time computable. -/
theorem pt_twd (T : TW) : PolyTimeComputable (twd Cw cw T) := by
  cases T
  · exact pt_vt
  · exact pt_inc.comp pt_vt
  · exact pt_rep Cw cw false
  · exact pt_rep Cw cw true

/-- Every offset word of an instance is polynomial-time computable. -/
theorem pt_awd (A : AW) : PolyTimeComputable (awd Cw cw A) := by
  cases A
  · exact pt_va
  · exact pt_inc.comp pt_va
  · exact pt_rep Cw cw false
  · exact pt_inc.comp (pt_rep Cw cw false)
  · exact pt_bjw
  · exact pt_inc.comp pt_bjw

/-- The description of the circuit "output input bit `j`" on `n` inputs. -/
def idxDesc (n j : ℕ) : List Bool :=
  List.replicate n true ++ false :: false :: (List.replicate j true ++ [false])

end Complexity.Meyer
