/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Candidates.Arithmetic
import TCSlib.Cryptography.Candidates.DiscreteLog
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Hashing.FromDiscreteLog.Encoding
import TCSlib.Complexity.Randomized.Closure

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The discrete-logarithm reduction's machine

The reduction runs a collision finder on the supplied key, reads its two padded
domain inputs, and writes their exponent difference modulo the supplied order.
Its arithmetic uses the polynomial-time bundle and its coins and advice are the
collision finder's coins and advice.

## Main definitions

* `modularDifference` computes a subtraction modulo an encoded order.
* `collisionPost` reads the key and padded finder output and selects the difference.
* `reductionRaw`, `collisionReduction` run the finder and apply the postprocessor.

## Main results

* `polyTimeComputable_collisionPost` proves postprocessing is polynomial-time.
* `collisionPost_ofFn_append` reads the postprocessor on two fixed-width inputs.
* `collisionPost_split` reads the postprocessor on an arbitrary raw finder output.
* `collisionReduction_runAtL` gives the reduction's exact activation.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January
  2010, §5.5.2, proof of Theorem 142.3.
-/

namespace TCSlib.Cryptography.Authentication.FromDiscreteLog

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates

/-- The encoded modular difference of `a` and `b` modulo `m` is computed as
`(a + (m - b)) mod m`, using truncated natural subtraction. When `b ≤ m`, this
represents the group difference; the output has the width of `m`. -/
def modularDifference (a b m : List Bool) : List Bool :=
  pairSndD (divModStr (pairEncode
    (addStr (pairEncode a (subStr (pairEncode m b)))) m))

/-- The modular-difference routine adds `a` to the truncated subtraction of `b`
from `m`, divides by `m`, and keeps the remainder. -/
theorem modularDifference_eq (a b m : List Bool) :
    modularDifference a b m =
      pairSndD (divModStr (pairEncode
        (addStr (pairEncode a (subStr (pairEncode m b)))) m)) := rfl

/-- The modular-difference routine writes the `|m|`-bit numeral of
`(⟦a⟧ + (⟦m⟧ - ⟦b⟧)) mod ⟦m⟧`. -/
theorem modularDifference_value (a b m : List Bool) :
    modularDifference a b m = natToList m.length
      ((NumberTheory.listToNat a +
        (NumberTheory.listToNat m - NumberTheory.listToNat b)) % NumberTheory.listToNat m) := by
  rw [modularDifference_eq, divModStr_pairEncode, pairSndD_pairEncode,
    listToNat_addStr, listToNat_subStr]

/-- Applying the modular-difference routine to three polynomial-time word functions
is polynomial-time under the arithmetic bundle. -/
theorem polyTimeComputable_modularDifference (H : ArithmeticFP)
    {a b m : List Bool → List Bool} (ha : PolyTimeComputable a)
    (hb : PolyTimeComputable b) (hm : PolyTimeComputable m) :
    PolyTimeComputable fun w => modularDifference (a w) (b w) (m w) := by
  have hs := H.sub.comp (hm.pairEncode hb)
  have hadd := H.add.comp (ha.pairEncode hs)
  have h := polyTimeComputable_pairSndD.comp (H.divMod.comp (hadd.pairEncode hm))
  refine h.congr fun w => ?_
  simp only [Function.comp_apply, modularDifference_eq]

/-- On `⟨u, ⟨⟨i,y⟩, raw⟩⟩`, pad or truncate `raw` to two blocks of `|u|+1` bits.
Read exponents from each block's first `|u|` bits and the first selector from its
last bit. Output `x' - x mod m` if that selector is true and `x - x' mod m`
otherwise, where `m` is the order word in the index `i` [PS10, Theorem 142.3]. -/
def collisionPost (w : List Bool) : List Bool :=
  let u := pairFstD w
  let key := pairFstD (pairSndD w)
  let raw := pairSndD (pairSndD w)
  let m := pairFstD (pairSndD (pairFstD key))
  let padded := padStr (.add (.add .var (.const 1)) (.add .var (.const 1))) u raw
  let x := padded.take u.length
  let x' := (padded.drop (u.length + 1)).take u.length
  if (padded.drop u.length).headD false then modularDifference x' x m
  else modularDifference x x' m

/-- The postprocessor pads the raw output, reads two exponent prefixes and the first
selector, and applies the corresponding modular difference. -/
theorem collisionPost_eq (w : List Bool) :
    collisionPost w =
      let u := pairFstD w
      let key := pairFstD (pairSndD w)
      let raw := pairSndD (pairSndD w)
      let m := pairFstD (pairSndD (pairFstD key))
      let padded := padStr (.add (.add .var (.const 1)) (.add .var (.const 1))) u raw
      let x := padded.take u.length
      let x' := (padded.drop (u.length + 1)).take u.length
      if (padded.drop u.length).headD false then modularDifference x' x m
      else modularDifference x x' m := rfl

/-- The collision postprocessor is polynomial-time under the arithmetic bundle.

**Proof sketch.** Pair projections read the parameter, raw output, and order word.
The existing padding and polynomial-prefix cuts read the two exponents and selector.
Both branches are compositions of subtraction, addition, and division, and the
existing conditional constructor chooses between them. -/
theorem polyTimeComputable_collisionPost (H : ArithmeticFP) :
    PolyTimeComputable collisionPost := by
  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
  have hu := polyTimeComputable_pairFstD
  have hkey := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hraw := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hm : PolyTimeComputable fun w =>
      pairFstD (pairSndD (pairFstD (pairFstD (pairSndD w)))) := by
    exact polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairFstD.comp hkey))
  have hpad : PolyTimeComputable fun w =>
      padStr width (pairFstD w) (pairSndD (pairSndD w)) := by
    convert (polyTimeComputable_padStr width).comp (hu.pairEncode hraw) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hx : PolyTimeComputable fun w =>
      (padStr width (pairFstD w) (pairSndD (pairSndD w))).take (pairFstD w).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp (hu.pairEncode hpad) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have hdrop : PolyTimeComputable fun w =>
      (padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
        ((pairFstD w).length + 1) := by
    convert (polyTimeComputable_pairDropPoly (.add .var (.const 1))).comp
      (hu.pairEncode hpad) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
      PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  have hx' : PolyTimeComputable fun w =>
      ((padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
        ((pairFstD w).length + 1)).take (pairFstD w).length := by
    convert (polyTimeComputable_pairTakePoly .var).comp (hu.pairEncode hdrop) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have htail : PolyTimeComputable fun w =>
      (padStr width (pairFstD w) (pairSndD (pairSndD w))).drop (pairFstD w).length := by
    convert (polyTimeComputable_pairDropPoly .var).comp (hu.pairEncode hpad) using 1
    funext w
    simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have hselector : PolyTimeComputable fun w =>
      [((padStr width (pairFstD w) (pairSndD (pairSndD w))).drop
        (pairFstD w).length).headD false] :=
    polyTimeComputable_headD.comp htail
  have h := polyTimeComputable_ite hselector
    (polyTimeComputable_modularDifference H hx' hx hm)
    (polyTimeComputable_modularDifference H hx hx' hm)
  exact h

/-- At a well-formed index, postprocessing the concatenation of two `(n + 1)`-bit
inputs writes the `n`-bit numeral of their selected exponent difference modulo
`dlM i`. The first input's final bit chooses `x' - x` when true and `x - x'`
otherwise [PS10, proof of Theorem 142.3].

**Proof sketch.** The concatenation already has the padding width. Cutting after
`n + 1` bits separates the two inputs, and their first `n` bits give the exponent
words. The input decomposition identifies the selector. Well-formedness supplies
the order word's width, and the arithmetic reader evaluates each difference. -/
theorem collisionPost_ofFn_append (n : ℕ) (i y : List Bool)
    (x x' : Fin (n + 1) → Bool) (hw : WellFormedIndex n i) :
    collisionPost (pairEncode (List.replicate n true)
      (pairEncode (pairEncode i y) (List.ofFn x ++ List.ofFn x'))) =
      natToList n (if x (Fin.last n) then
        (NumberTheory.listToNat ((List.ofFn x').take n) +
          (dlM i - NumberTheory.listToNat ((List.ofFn x).take n))) % dlM i
        else (NumberTheory.listToNat ((List.ofFn x).take n) +
          (dlM i - NumberTheory.listToNat ((List.ofFn x').take n))) % dlM i) := by
  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
  have hlen : (List.ofFn x ++ List.ofFn x').length =
      width.eval (List.replicate n true).length := by
    simp only [width, List.length_append, List.length_ofFn, List.length_replicate,
      PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  have hpad : padStr width (List.replicate n true) (List.ofFn x ++ List.ofFn x') =
      List.ofFn x ++ List.ofFn x' := by
    rw [padStr_of_length_le _ _ _ hlen.le, hlen, Nat.sub_self,
      List.replicate_zero, List.append_nil]
  dsimp only [width] at hpad
  have hprefix : n ≤ (List.ofFn x).length := by
    rw [List.length_ofFn]
    omega
  have hfirst : (List.ofFn x ++ List.ofFn x').take n = (List.ofFn x).take n :=
    List.take_append_of_le_length hprefix
  have hsecond : ((List.ofFn x ++ List.ofFn x').drop (n + 1)).take n =
      (List.ofFn x').take n := by
    rw [List.drop_left' (show (List.ofFn x).length = n + 1 by rw [List.length_ofFn])]
  have hselector : ((List.ofFn x ++ List.ofFn x').drop n).headD false =
      x (Fin.last n) := by
    rw [List.drop_append_of_le_length hprefix, inputWord_drop]
    rfl
  have hmw : (pairFstD (pairSndD i)).length = n := by
    obtain ⟨a, b, c, he, _, hb, _⟩ := (wellFormedIndex_iff n i).1 hw
    rw [he, pairSndD_pairEncode, pairFstD_pairEncode]
    exact hb
  simp only [collisionPost_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate, hpad, hfirst, hsecond, hselector]
  simp only [modularDifference_value, hmw, ← dlM_eq i]
  split_ifs <;> rfl

/-- For any raw finder output, the postprocessor writes the selected difference
of the two inputs obtained by the collision game's padding and splitting. It writes
`x' - x mod m` when the first selector is true and `x - x' mod m` otherwise
[PS10, proof of Theorem 142.3].

**Proof sketch.** The words of the two split inputs concatenate to the padded raw
word. Padding that word again does not change it, by the published padding/encoding
readers and the fact that padding an encoded vector recovers the vector. Thus the
fixed-width postprocessor contract applies to the two split inputs. -/
theorem collisionPost_split (n : ℕ) (i y raw : List Bool) (hw : WellFormedIndex n i) :
    let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
    collisionPost (pairEncode (List.replicate n true)
      (pairEncode (pairEncode i y) raw)) =
      natToList n (if xx.1 (Fin.last n) then
        (NumberTheory.listToNat ((List.ofFn xx.2).take n) +
          (dlM i - NumberTheory.listToNat ((List.ofFn xx.1).take n))) % dlM i
        else (NumberTheory.listToNat ((List.ofFn xx.1).take n) +
          (dlM i - NumberTheory.listToNat ((List.ofFn xx.2).take n))) % dlM i) := by
  let width : PolyExpr := .add (.add .var (.const 1)) (.add .var (.const 1))
  let u := List.replicate n true
  let xx := splitBits (a := n + 1) (b := n + 1) (padFin ((n + 1) + (n + 1)) raw)
  have hsplit : List.ofFn xx.1 ++ List.ofFn xx.2 =
      List.ofFn (padFin ((n + 1) + (n + 1)) raw) := by
    change List.ofFn (splitBits (a := n + 1) (b := n + 1)
      (padFin ((n + 1) + (n + 1)) raw)).1 ++
      List.ofFn (splitBits (a := n + 1) (b := n + 1)
        (padFin ((n + 1) + (n + 1)) raw)).2 = _
    rw [ofFn_splitBits_fst, ofFn_splitBits_snd, List.take_append_drop]
  have hword : List.ofFn (padFin ((n + 1) + (n + 1)) raw) = padStr width u raw := by
    have hwidth : width.eval u.length = ((n + 1) + (n + 1)) := by
      simp only [width, u, List.length_replicate, PolyExpr.eval_add, PolyExpr.eval_var,
        PolyExpr.eval_const]
    exact (congrArg (fun k : ℕ => List.ofFn (padFin k raw)) hwidth).symm.trans
      (ofFn_padFin_eq_padStr width u raw)
  have hidem : padStr width u (padStr width u raw) = padStr width u raw := by
    calc
      padStr width u (padStr width u raw) =
          List.ofFn (padFin (width.eval u.length) (padStr width u raw)) :=
        (ofFn_padFin_eq_padStr width u _).symm
      _ = List.ofFn (padFin (width.eval u.length)
          (List.ofFn (padFin (width.eval u.length) raw))) := by
        rw [← ofFn_padFin_eq_padStr width u raw]
      _ = List.ofFn (padFin (width.eval u.length) raw) := by rw [padFin_ofFn]
      _ = padStr width u raw := ofFn_padFin_eq_padStr width u raw
  have hpost : collisionPost (pairEncode u (pairEncode (pairEncode i y) raw)) =
      collisionPost (pairEncode u
        (pairEncode (pairEncode i y) (List.ofFn xx.1 ++ List.ofFn xx.2))) := by
    rw [hsplit, hword]
    dsimp only [width] at hidem
    dsimp only [width]
    simp only [collisionPost_eq, pairFstD_pairEncode, pairSndD_pairEncode, hidem]
  exact hpost.trans (collisionPost_ofFn_append n i y xx.1 xx.2 hw)

/-- On a raw NUPPT layout, run `A` and apply `collisionPost` to the parameter,
the original key, and `A`'s raw output [PS10, proof of Theorem 142.3]. -/
def reductionRaw (A : NUPPT) (z : List Bool) : List Bool :=
  collisionPost (pairEncode (NUPPT.inParam z) (pairEncode (NUPPT.inArg z) (A.output z)))

/-- The raw reduction passes its parameter and original argument together with
the finder's raw output to the postprocessor. -/
theorem reductionRaw_eq (A : NUPPT) (z : List Bool) :
    reductionRaw A z =
      collisionPost (pairEncode (NUPPT.inParam z)
        (pairEncode (NUPPT.inArg z) (A.output z))) := rfl

/-- Running a polynomial-time finder and then postprocessing its output is
polynomial-time under the arithmetic bundle. -/
theorem polyTimeComputable_reductionRaw (H : ArithmeticFP) (A : NUPPT) :
    PolyTimeComputable (reductionRaw A) := by
  have h := (polyTimeComputable_collisionPost H).comp
    (NUPPT.polyTimeComputable_inParam.pairEncode
      (NUPPT.polyTimeComputable_inArg.pairEncode A.polyTimeComputable_output))
  refine h.congr fun z => ?_
  simp only [Function.comp_apply, reductionRaw_eq]

/-- The discrete-log reduction runs the collision finder and extracts the exponent
difference, using the same coins and advice [PS10, proof of Theorem 142.3]. -/
noncomputable def collisionReduction (H : ArithmeticFP) (A : NUPPT) : NUPPT :=
  NUPPT.ofPolyTime (polyTimeComputable_reductionRaw H A)
    A.coins A.adv A.advice A.advice_length

/-- The reduction is the polynomial-time realization of `reductionRaw A`, with
the finder's coin polynomial, advice bound, and advice function. -/
theorem collisionReduction_eq (H : ArithmeticFP) (A : NUPPT) :
    collisionReduction H A = NUPPT.ofPolyTime (polyTimeComputable_reductionRaw H A)
      A.coins A.adv A.advice A.advice_length := rfl

/-- The reduction uses the collision finder's coin polynomial. -/
theorem collisionReduction_coins (H : ArithmeticFP) (A : NUPPT) :
    (collisionReduction H A).coins = A.coins := by
  rw [collisionReduction_eq, NUPPT.coins_ofPolyTime]

/-- The reduction has the collision finder's advice bound. -/
theorem collisionReduction_adv (H : ArithmeticFP) (A : NUPPT) :
    (collisionReduction H A).adv = A.adv := by
  rw [collisionReduction_eq, NUPPT.adv_ofPolyTime]

/-- The reduction uses the collision finder's advice at every parameter. -/
theorem collisionReduction_advice (H : ArithmeticFP) (A : NUPPT) :
    (collisionReduction H A).advice = A.advice := by
  rw [collisionReduction_eq, NUPPT.advice_ofPolyTime]

/-- At parameter `n` on key `key` and coin list `r`, the reduction postprocesses
`A.runAtL n key r` while retaining `1^n` and the original key. -/
theorem collisionReduction_runAtL (H : ArithmeticFP) (A : NUPPT)
    (n : ℕ) (key r : List Bool) :
    (collisionReduction H A).runAtL n key r =
      collisionPost (pairEncode (List.replicate n true)
        (pairEncode key (A.runAtL n key r))) := by
  rw [collisionReduction_eq, NUPPT.runAtL_ofPolyTime, reductionRaw_eq]
  simp only [NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.advInput_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, NUPPT.runAtL_eq]

/-- On typed coins, the reduction postprocesses the finder's output on the same
coin string, transported along the equality of their coin polynomials. -/
theorem collisionReduction_runAt (H : ArithmeticFP) (A : NUPPT)
    (n : ℕ) (key : List Bool) (r : (collisionReduction H A).Coins n) :
    (collisionReduction H A).runAt n key r =
      collisionPost (pairEncode (List.replicate n true)
        (pairEncode key (A.runAt n key
          (NUPPT.coinsCongr (collisionReduction_coins H A) n r)))) := by
  rw [NUPPT.runAt_eq, collisionReduction_runAtL, NUPPT.runAt_eq,
    NUPPT.coinsCongr_ofFn]

end TCSlib.Cryptography.Authentication.FromDiscreteLog
