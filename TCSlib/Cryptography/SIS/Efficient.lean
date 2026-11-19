/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SIS.Assumption
import TCSlib.Cryptography.CoinSampling.Contract
import TCSlib.Cryptography.Encoding.BinaryArith
import TCSlib.Complexity.ClassP.BinaryArith.PrimeFind
import TCSlib.Complexity.Randomized.Primitives

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Efficient SIS families: a uniform parameter map

`SIS.Family` (`SIS/Assumption.lean`) carries no efficiency. Under rule 15 (efficiency is part of
the definition of every primitive), every scheme instance built on SIS requires an
`EfficientFamily`: an `SIS.Family` with a **uniform parameter map**, one polynomial-time string
map sending `1^κ` to the parameter word `⟨1^n, ⟨1^m, ⟨⦃q⦄, ⦃β⦄⟩⟩⟩` of the family's parameters
(`Parameters.encode`). Uniform matrices modulo a `q` read from that word are already efficient
(`CoinSampling.samplesEfficiently_residue`), so no sampler field is needed.

`SISAssumption` stays on the raw `Family`: consumers write `SISAssumption F.toFamily`.

## Main definitions

* `Parameters.encode w b P`: the parameter word `⟨1^n, ⟨1^m, ⟨⦃q⦄_{w+1}, ⦃β⦄_b⟩⟩⟩`.
* `EfficientFamily`: `Family` with `params_uniform`.
* `dyadicScheduleParameters`, `dyadicScheduleFamily`, `EfficientFamily.ofDyadic`: the
  polynomially scheduled dyadic families.
* `dyadicExample`: one non-vacuity instance (no hardness claimed).

## Main results

* `Parameters.encode_injective`: the word determines the parameters.
* `params_uniform_of_schedule`: the parameter map of a schedule `n = N(κ)`, `m = M(κ)`,
  `q = 2^{W(κ)}`, `β = S(κ)` is uniform.

## References

* [Pei16] C. Peikert, *A Decade of Lattice Cryptography*, author version dated
  17 February 2016, Definition 4.1.1 (SIS).
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 23.4 (one machine, uniform coins) and Definition 26.8 (non-uniform PPT).

**Convention.** The structure is a repository convention (rule 15, ruling Q3 A): [Pei16] states
the families without an efficiency clause. No hardness is asserted anywhere in this file. The
dyadic schedule here is local; the hashing profile `Hashing.SIS.dyadicFamily` is not used.

**Import.** The numeral of `2^W` and its polynomial-time writer
(`CoinSampling.natToList_two_pow`, `CoinSampling.polyTimeComputable_twoPowWord`) come from the
shared sampler contract `CoinSampling/Contract.lean`; the file does not import the LWE layer, and
SIS hardness stays independent of LWE.
-/

namespace TCSlib.Cryptography.SIS

open Complexity Turing

/-! ### The parameter word -/

/-- **The parameter word** of SIS parameters at modulus width `w` and bound width `b`:
`⟨1^n, ⟨1^m, ⟨⦃q⦄_{w+1}, ⦃β⦄_b⟩⟩⟩`, the row and column counts in unary, the modulus as an
MSB-first numeral of width `w + 1` (the width of `CoinSampling.modulusWord`) and the
squared-norm bound `β` as a numeral of width `b`. Glue: rule 15's parameter word;
[Pei16, Definition 4.1.1] fixes the parameters, not their encoding. -/
def Parameters.encode (w b : ℕ) (P : Parameters) : List Bool :=
  pairEncode (List.replicate P.dimension true)
    (pairEncode (List.replicate P.columns true)
      (pairEncode (Candidates.natToList (w + 1) P.modulus)
        (Candidates.natToList b P.sqNormBound)))

/-- `P.encode w b = ⟨1^n, ⟨1^m, ⟨natToList (w + 1) q, natToList b β⟩⟩⟩`. -/
theorem Parameters.encode_eq (w b : ℕ) (P : Parameters) :
    P.encode w b = pairEncode (List.replicate P.dimension true)
      (pairEncode (List.replicate P.columns true)
        (pairEncode (Candidates.natToList (w + 1) P.modulus)
          (Candidates.natToList b P.sqNormBound))) := rfl

/-- **The parameter word determines the parameters**: for moduli at most `2^w` and bounds below
`2^b`, `P.encode w b = P'.encode w b` implies `P = P'`. Glue.

**Proof sketch.** The projections of the nested pair give the unary counts (equal lengths) and
the two numerals, which are injective below `2^{w+1}` and `2^b` (`Candidates.natToList_injOn`).
The parameters are then equal field by field. -/
theorem Parameters.encode_injective {w b : ℕ} {P P' : Parameters} (hP : P.modulus ≤ 2 ^ w)
    (hP' : P'.modulus ≤ 2 ^ w) (hβ : P.sqNormBound < 2 ^ b) (hβ' : P'.sqNormBound < 2 ^ b)
    (h : P.encode w b = P'.encode w b) : P = P' := by
  have hlt : ∀ q : ℕ, q ≤ 2 ^ w → q < 2 ^ (w + 1) := fun q hq =>
    hq.trans_lt (Nat.pow_lt_pow_right (by norm_num) (Nat.lt_succ_self w))
  rw [Parameters.encode_eq, Parameters.encode_eq] at h
  have h1 := congrArg pairFstD h
  have h2 := congrArg (fun z => pairFstD (pairSndD z)) h
  have h3 := congrArg (fun z => pairFstD (pairSndD (pairSndD z))) h
  have h4 := congrArg (fun z => pairSndD (pairSndD (pairSndD z))) h
  simp only [pairFstD_pairEncode, pairSndD_pairEncode] at h1 h2 h3 h4
  have hn := congrArg List.length h1
  have hm := congrArg List.length h2
  rw [List.length_replicate, List.length_replicate] at hn hm
  have hq := Candidates.natToList_injOn (hlt _ hP) (hlt _ hP') h3
  have hb := Candidates.natToList_injOn hβ hβ' h4
  obtain ⟨n, m, q, β, h2q⟩ := P
  obtain ⟨n', m', q', β', h2q'⟩ := P'
  dsimp only at hn hm hq hb
  subst hn hm hq hb
  rfl

/-- The first component of the parameter word is `1^n`. -/
theorem Parameters.pairFstD_encode (w b : ℕ) (P : Parameters) :
    pairFstD (P.encode w b) = List.replicate P.dimension true := by
  rw [Parameters.encode_eq, pairFstD_pairEncode]

/-- The second component of the parameter word starts with `1^m`. -/
theorem Parameters.pairFstD_pairSndD_encode (w b : ℕ) (P : Parameters) :
    pairFstD (pairSndD (P.encode w b)) = List.replicate P.columns true := by
  rw [Parameters.encode_eq, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The modulus component of the parameter word is `⦃q⦄_{w+1}`. -/
theorem Parameters.modulus_encode (w b : ℕ) (P : Parameters) :
    pairFstD (pairSndD (pairSndD (P.encode w b))) = Candidates.natToList (w + 1) P.modulus := by
  rw [Parameters.encode_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairFstD_pairEncode]

/-- The bound component of the parameter word is `⦃β⦄_b`. -/
theorem Parameters.sqNormBound_encode (w b : ℕ) (P : Parameters) :
    pairSndD (pairSndD (pairSndD (P.encode w b))) = Candidates.natToList b P.sqNormBound := by
  rw [Parameters.encode_eq, pairSndD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

/-! ### The efficient family -/

/-- **An efficient SIS family** (rule 15, ruling Q3 A): an SIS family [Pei16, Definition 4.1.1]
with `params_uniform`, one polynomial-time map `f` with
`f (1^κ) = (parameters κ).encode (r(κ)) (b(κ))`, `r = residueBits`, `b = magnitudeBits`
(uniform: no advice, no κ-indexed program [PS10, Definition 23.4]).

Glue: rule 15's efficiency-in-the-definition form; [Pei16] states the families without an
efficiency clause. No hardness is asserted: `SISAssumption F.toFamily` is a separate
hypothesis. -/
structure EfficientFamily extends Family where
  /-- The parameter word at the representation widths is uniformly computable from `1^κ`. -/
  params_uniform : ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
    ∀ κ, f (List.replicate κ true) =
      (parameters κ).encode (residueBits.eval κ) (magnitudeBits.eval κ)

/-! ### Uniform schedules -/

/-- **The numeral of a polynomial value is polynomial-time**: `x ↦ ⦃S(|x|)⦄_{B(|x|)}`, by the
unary word `1^{S(|x|)}` (`polyTimeComputable_unaryPoly`), its binary length
(`BinArith.countLoop`) and the MSB adapter `Encoding.BinaryArith.fromLEPoly B`. Glue. -/
theorem polyTimeComputable_numeralPoly (S B : PolyExpr) :
    PolyTimeComputable fun x : List Bool =>
      Candidates.natToList (B.eval x.length) (S.eval x.length) := by
  have h := (Encoding.BinaryArith.polyTimeComputable_fromLEPoly B).comp'
    (polyTimeComputable_id.pairEncode (polyTimeComputable_pairFstD.comp'
      (BinArith.polyTimeComputable_countLoop.comp' (polyTimeComputable_unaryPoly S))))
  refine h.congr fun x => ?_
  dsimp only
  rw [BinArith.countLoop_eq, pairFstD_pairEncode, List.length_replicate,
    Encoding.BinaryArith.fromLEPoly_pairEncode, LogProg.bitsVal_bits]
  rfl

/-- **A polynomial dyadic schedule has a uniform parameter map**: if `n(κ) = N(κ)`,
`m(κ) = M(κ)`, `q(κ) = 2^{W(κ)}` and `β(κ) = S(κ)`, one polynomial-time map sends `1^κ` to
`(P κ).encode (W(κ)) (B(κ))`. Glue.

**Proof sketch.** The map writes `⟨1^{N(|x|)}, ⟨1^{M(|x|)}, ⟨1 0^{W(|x|)}, ⦃S(|x|)⦄_{B(|x|)}⟩⟩⟩`:
the unary words by `polyTimeComputable_unaryPoly`, `1 0^W = ⦃2^W⦄_{W+1}`
(`CoinSampling.natToList_two_pow`) by `CoinSampling.polyTimeComputable_twoPowWord`, the bound by
`polyTimeComputable_numeralPoly`, the pairs by `PolyTimeComputable.pairEncode`. On `1^κ` the
length is `κ`. -/
theorem params_uniform_of_schedule (N M W S B : PolyExpr) (P : ℕ → Parameters)
    (hn : ∀ κ, (P κ).dimension = N.eval κ) (hm : ∀ κ, (P κ).columns = M.eval κ)
    (hq : ∀ κ, (P κ).modulus = 2 ^ W.eval κ) (hβ : ∀ κ, (P κ).sqNormBound = S.eval κ) :
    ∃ f : List Bool → List Bool, PolyTimeComputable f ∧
      ∀ κ, f (List.replicate κ true) = (P κ).encode (W.eval κ) (B.eval κ) := by
  refine ⟨fun x => pairEncode (List.replicate (N.eval x.length) true)
    (pairEncode (List.replicate (M.eval x.length) true)
      (pairEncode (true :: List.replicate (W.eval x.length) false)
        (Candidates.natToList (B.eval x.length) (S.eval x.length)))),
    (polyTimeComputable_unaryPoly N).pairEncode ((polyTimeComputable_unaryPoly M).pairEncode
      ((CoinSampling.polyTimeComputable_twoPowWord W).pairEncode
        (polyTimeComputable_numeralPoly S B))),
    fun κ => ?_⟩
  dsimp only
  rw [List.length_replicate, Parameters.encode_eq, hn, hm, hq, hβ, CoinSampling.natToList_two_pow]

/-! ### Dyadic schedules -/

/-- **Dyadic SIS parameters** of a schedule: `n = N(κ)` rows, `m = M(κ)` columns,
`q = 2^{W(κ)}` (for `W ≥ 1`, so `q ≥ 2`) and squared-norm bound `β = S(κ)`. Glue: the
power-of-two moduli of the exact fair-bit route (`SIS/Assumption.lean`, convention note). -/
def dyadicScheduleParameters (N M W S : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ) (κ : ℕ) :
    Parameters where
  dimension := N.eval κ
  columns := M.eval κ
  modulus := 2 ^ W.eval κ
  sqNormBound := S.eval κ
  modulus_ge_two := by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ W.eval κ := Nat.pow_le_pow_right (by norm_num) (hW κ)

/-- The row count of `dyadicScheduleParameters N M W S hW κ` is `N(κ)`. -/
theorem dyadicScheduleParameters_dimension (N M W S : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (κ : ℕ) : (dyadicScheduleParameters N M W S hW κ).dimension = N.eval κ := rfl

/-- The column count of `dyadicScheduleParameters N M W S hW κ` is `M(κ)`. -/
theorem dyadicScheduleParameters_columns (N M W S : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (κ : ℕ) : (dyadicScheduleParameters N M W S hW κ).columns = M.eval κ := rfl

/-- The modulus of `dyadicScheduleParameters N M W S hW κ` is `2^{W(κ)}`. -/
theorem dyadicScheduleParameters_modulus (N M W S : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (κ : ℕ) : (dyadicScheduleParameters N M W S hW κ).modulus = 2 ^ W.eval κ := rfl

/-- The squared-norm bound of `dyadicScheduleParameters N M W S hW κ` is `S(κ)`. -/
theorem dyadicScheduleParameters_sqNormBound (N M W S : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (κ : ℕ) : (dyadicScheduleParameters N M W S hW κ).sqNormBound = S.eval κ := rfl

/-- **The dyadic SIS family** of a schedule `(N, M, W, S)` with magnitude width `B`
(`S(κ) < 2^{B(κ)}`): parameters `dyadicScheduleParameters N M W S hW`, bounds `N`, `M`, residue
width `W` (so `q = 2^W` fits exactly) [Pei16, Definition 4.1.1, power-of-two moduli]. -/
def dyadicScheduleFamily (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) : Family where
  parameters := dyadicScheduleParameters N M W S hW
  dimensionBound := N
  columnsBound := M
  residueBits := W
  magnitudeBits := B
  dimension_le κ := (dyadicScheduleParameters_dimension N M W S hW κ).le
  columns_le κ := (dyadicScheduleParameters_columns N M W S hW κ).le
  modulus_le_pow κ := (dyadicScheduleParameters_modulus N M W S hW κ).le
  sqNormBound_lt_pow κ := (dyadicScheduleParameters_sqNormBound N M W S hW κ).trans_lt (hSB κ)

/-- The parameters of `dyadicScheduleFamily N M W S B hW hSB` are
`dyadicScheduleParameters N M W S hW`. -/
theorem dyadicScheduleFamily_parameters (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) :
    (dyadicScheduleFamily N M W S B hW hSB).parameters = dyadicScheduleParameters N M W S hW :=
  rfl

/-- The residue width of `dyadicScheduleFamily N M W S B hW hSB` is `W`. -/
theorem dyadicScheduleFamily_residueBits (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) :
    (dyadicScheduleFamily N M W S B hW hSB).residueBits = W := rfl

/-- The magnitude width of `dyadicScheduleFamily N M W S B hW hSB` is `B`. -/
theorem dyadicScheduleFamily_magnitudeBits (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) :
    (dyadicScheduleFamily N M W S B hW hSB).magnitudeBits = B := rfl

/-- The dimension bound of `dyadicScheduleFamily N M W S B hW hSB` is `N`. -/
theorem dyadicScheduleFamily_dimensionBound (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) :
    (dyadicScheduleFamily N M W S B hW hSB).dimensionBound = N := rfl

/-- The column bound of `dyadicScheduleFamily N M W S B hW hSB` is `M`. -/
theorem dyadicScheduleFamily_columnsBound (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) :
    (dyadicScheduleFamily N M W S B hW hSB).columnsBound = M := rfl

/-- **The efficient dyadic SIS family** of a schedule (`dyadicScheduleFamily`, its parameter map
by `params_uniform_of_schedule`). No hardness is claimed. Glue. -/
def EfficientFamily.ofDyadic (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) : EfficientFamily where
  toFamily := dyadicScheduleFamily N M W S B hW hSB
  params_uniform := by
    rw [dyadicScheduleFamily_parameters, dyadicScheduleFamily_residueBits,
      dyadicScheduleFamily_magnitudeBits]
    exact params_uniform_of_schedule N M W S B _ (dyadicScheduleParameters_dimension N M W S hW)
      (dyadicScheduleParameters_columns N M W S hW) (dyadicScheduleParameters_modulus N M W S hW)
      (dyadicScheduleParameters_sqNormBound N M W S hW)

/-- The family of `EfficientFamily.ofDyadic N M W S B hW hSB` is
`dyadicScheduleFamily N M W S B hW hSB`. -/
theorem EfficientFamily.ofDyadic_toFamily (N M W S B : PolyExpr) (hW : ∀ κ, 1 ≤ W.eval κ)
    (hSB : ∀ κ, S.eval κ < 2 ^ B.eval κ) :
    (EfficientFamily.ofDyadic N M W S B hW hSB).toFamily =
      dyadicScheduleFamily N M W S B hW hSB := rfl

/-! ### Non-vacuity -/

/-- **A non-vacuity instance** of `EfficientFamily`: `n = κ + 1` rows, `m = 2(κ + 1)²` columns,
`q = 2^{κ+1}`, squared-norm bound `β = κ + 1` and magnitude width `κ + 1`
(`EfficientFamily.ofDyadic`). Its parameter map is proved uniform. **No hardness is claimed**:
this instance only shows that the structure is inhabited; `SISAssumption dyadicExample.toFamily`
is not asserted. Glue. -/
def dyadicExample : EfficientFamily :=
  EfficientFamily.ofDyadic (.add .var (.const 1)) (.mul (.const 2) (.pow (.add .var (.const 1)) 2))
    (.add .var (.const 1)) (.add .var (.const 1)) (.add .var (.const 1))
    (fun κ => by
      rw [PolyExpr.eval_add, PolyExpr.eval_const]
      exact Nat.le_add_left 1 _)
    fun κ => Nat.lt_two_pow_self

/-- The parameters of `dyadicExample` at `κ`: `κ + 1` rows, `2(κ + 1)²` columns, modulus
`2^{κ+1}` and squared-norm bound `κ + 1`. -/
theorem dyadicExample_parameters (κ : ℕ) :
    (dyadicExample.parameters κ).dimension = κ + 1 ∧
      (dyadicExample.parameters κ).columns = 2 * (κ + 1) ^ 2 ∧
      (dyadicExample.parameters κ).modulus = 2 ^ (κ + 1) ∧
      (dyadicExample.parameters κ).sqNormBound = κ + 1 := by
  have h : (PolyExpr.add .var (.const 1)).eval κ = κ + 1 := by
    rw [PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
  refine ⟨h, ?_, ?_, h⟩
  · show (PolyExpr.mul (.const 2) (.pow (.add .var (.const 1)) 2)).eval κ = 2 * (κ + 1) ^ 2
    rw [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_pow, h]
  · show 2 ^ (PolyExpr.add .var (.const 1)).eval κ = 2 ^ (κ + 1)
    rw [h]

end TCSlib.Cryptography.SIS
