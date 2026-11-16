/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.SuffixMachine
import TCSlib.Cryptography.Asymptotic.Adversary

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The advised computational sequential-phase reduction

A raw current-phase candidate is normalized using fixed metadata, followed by a randomized
simulated suffix and the original distinguisher. The metadata contains no witness. Validity
and reachability are properties of the later proof; every machine here uses total word
projections and the canonical normalizer on arbitrary inputs.

## Main definitions

* `reductionData`: common input, verifier auxiliary input/tape, phase, and raw prefix word.
* `phaseContinuation`: normalize the current candidate, simulate the suffix, and replay a view.

## Main results

* `phaseContinuation_poly`: the continuation is polynomial-time on total metadata functions.
* `exists_continuationSampler`: a uniform fresh-coin sampler for the continuation.
* `exists_phaseReduction`: compose the sampler with a distinguisher and bounded advice.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- For `x,z,rV,j,preWord`, the reduction metadata is
`⟨x,⟨z,⟨rV,⟨1^j,preWord⟩⟩⟩⟩`. Keeping the prefix as a raw word gives an exact advice-size
bound even on malformed metadata. [PS10, Theorem 175.1, phase-reduction advice].
`reductionData x z rV j preWord = pairEncode x (pairEncode z (pairEncode rV (pairEncode
(List.replicate j true) preWord)))`. -/
def reductionData (x z rV : List Bool) (j : ℕ) (preWord : List Bool) : List Bool :=
  pairEncode x (pairEncode z (pairEncode rV (pairEncode (List.replicate j true) preWord)))

/-- The metadata equation is `reductionData x z rV j preWord =
pairEncode x (pairEncode z (pairEncode rV (pairEncode (List.replicate j true) preWord)))`. -/
theorem reductionData_eq (x z rV : List Bool) (j : ℕ) (preWord : List Bool) :
    reductionData x z rV j preWord =
      pairEncode x (pairEncode z (pairEncode rV (pairEncode (List.replicate j true) preWord))) :=
  rfl

/-- The five projection fields of `reductionData x z rV j preWord`, in order, are
`x,z,rV,List.replicate j true,preWord`.
`pairFstD (reductionData x z rV j preWord) = x ∧ pairFstD (pairSndD (reductionData x z rV j
preWord)) = z ∧ pairFstD (pairSndD (pairSndD (reductionData x z rV j preWord))) = rV ∧ pairFstD
(pairSndD (pairSndD (pairSndD (reductionData x z rV …`. -/
theorem reductionData_fields (x z rV : List Bool) (j : ℕ) (preWord : List Bool) :
    pairFstD (reductionData x z rV j preWord) = x ∧
    pairFstD (pairSndD (reductionData x z rV j preWord)) = z ∧
    pairFstD (pairSndD (pairSndD (reductionData x z rV j preWord))) = rV ∧
    pairFstD (pairSndD (pairSndD (pairSndD (reductionData x z rV j preWord)))) =
      List.replicate j true ∧
    pairSndD (pairSndD (pairSndD (pairSndD (reductionData x z rV j preWord)))) = preWord := by
  simp only [reductionData_eq, pairFstD_pairEncode, pairSndD_pairEncode, and_self]

/-- For polynomial-time `X,Z,RV,PreWord` and unary polynomial-time `J`, the metadata map
`w ↦ reductionData (X w) (Z w) (RV w) (J w) (PreWord w)` is polynomial-time.
`PolyTimeComputable fun w => reductionData (X w) (Z w) (RV w) (J w) (PreWord w)`. -/
theorem reductionData_poly {X Z RV PreWord : List Bool → List Bool} {J : List Bool → ℕ}
    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z) (hRV : PolyTimeComputable RV)
    (hJ : PolyTimeComputable fun w => List.replicate (J w) true)
    (hPre : PolyTimeComputable PreWord) :
    PolyTimeComputable fun w => reductionData (X w) (Z w) (RV w) (J w) (PreWord w) :=
  (hX.pairEncode (hZ.pairEncode (hRV.pairEncode (hJ.pairEncode hPre)))).congr
    (fun _ => (reductionData_eq _ _ _ _ _).symm)

/-- The metadata length is
`|reductionData x z rV j preWord| = 2|x|+2|z|+2|rV|+2j+|preWord|+8`. -/
theorem reductionData_length (x z rV : List Bool) (j : ℕ) (preWord : List Bool) :
    (reductionData x z rV j preWord).length =
      2 * x.length + 2 * z.length + 2 * rV.length + 2 * j + preWord.length + 8 := by
  rw [reductionData_eq, length_pairEncode, length_pairEncode, length_pairEncode,
    length_pairEncode, List.length_replicate]
  omega

/-- For a canonical prefix word, reduction metadata is the input paired with the phase
auxiliary word: `reductionData x z rV j (encodeMsgs pre) = pairEncode x (phaseAux z rV j pre)`.
-/
theorem reductionData_encodeMsgs (x z rV : List Bool) (j : ℕ) (pre : List (List Bool)) :
    reductionData x z rV j (Strategy.encodeMsgs pre) = pairEncode x (phaseAux z rV j pre) :=
  (reductionData_eq _ _ _ _ _).trans (congrArg (pairEncode x) (phaseAux_eq z rV j pre).symm)

/-- For `S,k,B,Q,verifierFirst,x,z,rV,j,pre,raw,rS`, normalize the raw current-phase view
using known auxiliary input `phaseAux z rV j pre`, append the empty prover fillers, simulate
phases `j+1` through `Q(|x|)-1`, and return the canonical final view with fields `x,z,rV`.
All decoders and counts are total, including on malformed candidates and `j≥Q(|x|)`.
[PS10, Theorem 175.1; Gol01, §4.3.4, one-phase hybrid continuation]. -/
def phaseContinuation (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool)
    (x z rV : List Bool) (j : ℕ) (pre : List (List Bool)) (raw rS : List Bool) : List Bool :=
  let aux := phaseAux z rV j pre
  let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
  let pre1 := pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) raw ++
    List.replicate (k.eval x.length - p) [])
  View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV rS (j + 1) pre1
    (Q.eval x.length - (j + 1))⟩

/-- The complete `phaseContinuation` equation first forms
`pre1 = pre ++ (normalizePhaseMsgs x (phaseAux z rV j pre) p (B(|x|)) raw ++ (k(|x|)-p) empties)`,
then encodes `⟨x,z,rV,phaseSuffix … (j+1) pre1 (Q(|x|)-(j+1))⟩`, with
`p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`. -/
theorem phaseContinuation_eq (S : NUPPT) (k B Q : PolyExpr) (verifierFirst : Bool)
    (x z rV : List Bool) (j : ℕ) (pre : List (List Bool)) (raw rS : List Bool) :
    phaseContinuation S k B Q verifierFirst x z rV j pre raw rS =
      let aux := phaseAux z rV j pre
      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
      let pre1 := pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) raw ++
        List.replicate (k.eval x.length - p) [])
      View.encode ⟨x, z, rV, phaseSuffix S k B verifierFirst x z rV rS (j + 1) pre1
        (Q.eval x.length - (j + 1))⟩ := rfl

/-- For uniform `S`, fixed `k,B,Q,verifierFirst`, polynomial-time words `X,Z,RV,Raw,RS`,
unary polynomial-time phase `J`, and initial messages `H` with polynomial-time encoding,
`w ↦ phaseContinuation S k B Q verifierFirst (X w) (Z w) (RV w) (J w) (H w) (Raw w) (RS w)`
is polynomial-time. No validity, reachability, witness, or phase-range premise is required.
[PS10, Theorem 175.1, the one-phase hybrid machine].
`PolyTimeComputable fun w => phaseContinuation S k B Q verifierFirst (X w) (Z w) (RV w) (J w) (H w)
(Raw w) (RS w)`.

**Proof sketch.** Build the expected phase auxiliary word and canonically normalize the
current candidate. Append its real-message encoding and the existing empty-filler encoding
to the earlier prefix. Unary arithmetic computes starting phase `J+1` and remaining count
`Q(|X|)-(J+1)`. Apply the published arbitrary-prefix suffix machine, then assemble the
canonical final view through its equation reader. All preprocessing is total. -/
theorem phaseContinuation_poly (S : NUPPT) (hS : S.Uniform) (k B Q : PolyExpr)
    (verifierFirst : Bool) {X Z RV Raw RS : List Bool → List Bool} {J : List Bool → ℕ}
    {H : List Bool → List (List Bool)}
    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z) (hRV : PolyTimeComputable RV)
    (hRaw : PolyTimeComputable Raw) (hRS : PolyTimeComputable RS)
    (hJ : PolyTimeComputable fun w => List.replicate (J w) true)
    (hH : PolyTimeComputable fun w => Strategy.encodeMsgs (H w)) :
    PolyTimeComputable fun w => phaseContinuation S k B Q verifierFirst
      (X w) (Z w) (RV w) (J w) (H w) (Raw w) (RS w) := by
  -- Canonical normalization supplies the candidate phase's bounded real slots.
  have haux := phaseAux_poly hZ hRV hJ hH
  have hK := EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly hX)
  have hP : PolyTimeComputable fun w => List.replicate
      (if verifierFirst then k.eval (X w).length / 2 else (k.eval (X w).length + 1) / 2) true := by
    cases verifierFirst
    · simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly
        (EncodingMachines.unaryAdd_poly hK (EncodingMachines.unaryConst_poly 1))
        (EncodingMachines.unaryConst_poly 2)
    · simpa only [EncodingMachines.divNum_eq] using
        EncodingMachines.divNum_poly hK (EncodingMachines.unaryConst_poly 2)
  have hbits := EncodingMachines.unaryPolyOf_poly B (EncodingMachines.unaryLength_poly hX)
  have hnorm := polyTimeComputable_encode_normalizePhaseMsgs hX haux hRaw hP hbits
  have hfill := encode_emptyMsgs_poly (EncodingMachines.unarySub_poly hK hP)
  let H1 : List Bool → List (List Bool) := fun w =>
    H w ++ (normalizePhaseMsgs (X w) (phaseAux (Z w) (RV w) (J w) (H w))
      (if verifierFirst then k.eval (X w).length / 2 else (k.eval (X w).length + 1) / 2)
      (B.eval (X w).length) (Raw w) ++ List.replicate
        (k.eval (X w).length -
          (if verifierFirst then k.eval (X w).length / 2 else (k.eval (X w).length + 1) / 2)) [])
  have hH1 : PolyTimeComputable fun w => Strategy.encodeMsgs (H1 w) := by
    refine (hH.append (hnorm.append hfill)).congr fun w => ?_
    dsimp only [H1]
    rw [CommitmentLemmas.encodeMsgs_append, CommitmentLemmas.encodeMsgs_append]
  -- Reuse the total suffix routine after this candidate phase, then replay the view.
  have hStart := EncodingMachines.unaryAdd_poly hJ (EncodingMachines.unaryConst_poly 1)
  have hCount := EncodingMachines.unarySub_poly
    (EncodingMachines.unaryPolyOf_poly Q (EncodingMachines.unaryLength_poly hX)) hStart
  have hsuffix := phaseSuffix_poly S hS k B verifierFirst
    hX hZ hRV hRS hStart hCount hH1
  refine ((hX.pairEncode hZ).pairEncode (hRV.pairEncode hsuffix)).congr fun w => ?_
  rw [phaseContinuation_eq, View.encode_mk]

/-- For uniform `S` and `k,B,Q,verifierFirst`, there is a uniform sampler `U` with coins
`Q*S.coins` whose activation on `⟨raw,reductionData x z rV j preWord⟩` is exactly
`phaseContinuation S k B Q verifierFirst x z rV j (decWords preWord) raw r`.
This holds for every security parameter and every raw tape, without metadata validity tests.
[PS10, Theorem 175.1, randomized one-phase hybrid continuation].
`∃ U : NUPPT, U.Uniform ∧ U.coins = .mul Q S.coins ∧ ∀ (n : ℕ) (raw x z rV : List Bool) (j : ℕ)
(preWord r : List Bool), U.runAtL n (pairEncode raw (reductionData x z rV j preWord)) r =
phaseContinuation S k B Q verifierFirst x z rV j …`.

**Proof sketch.** Decode the metadata through total pair projections, its phase through
unary length, and its earlier prefix through the total word-list decoder. Apply
`phaseContinuation_poly` with the sampler's full coin tape. The published uniform-machine
constructor assigns the stated coin polynomial. Public activation/layout and metadata
readers give the exact equation, including malformed prefix words. -/
theorem exists_continuationSampler (S : NUPPT) (hS : S.Uniform) (k B Q : PolyExpr)
    (verifierFirst : Bool) :
    ∃ U : NUPPT, U.Uniform ∧ U.coins = .mul Q S.coins ∧
      ∀ (n : ℕ) (raw x z rV : List Bool) (j : ℕ) (preWord r : List Bool),
        U.runAtL n (pairEncode raw (reductionData x z rV j preWord)) r =
          phaseContinuation S k B Q verifierFirst x z rV j (BinArith.decWords preWord)
            raw r := by
  -- Decode only total metadata projections and the raw prefix interpretation.
  let M : List Bool → List Bool := fun w => pairSndD (NUPPT.inArg w)
  let X : List Bool → List Bool := fun w => pairFstD (M w)
  let Z : List Bool → List Bool := fun w => pairFstD (pairSndD (M w))
  let RV : List Bool → List Bool := fun w => pairFstD (pairSndD (pairSndD (M w)))
  let J : List Bool → ℕ := fun w =>
    (pairFstD (pairSndD (pairSndD (pairSndD (M w))))).length
  let PW : List Bool → List Bool := fun w =>
    pairSndD (pairSndD (pairSndD (pairSndD (M w))))
  let Raw : List Bool → List Bool := fun w => pairFstD (NUPPT.inArg w)
  have hM : PolyTimeComputable M :=
    polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hX : PolyTimeComputable X := polyTimeComputable_pairFstD.comp hM
  have hZ : PolyTimeComputable Z :=
    polyTimeComputable_pairFstD.comp (polyTimeComputable_pairSndD.comp hM)
  have hRV : PolyTimeComputable RV := polyTimeComputable_pairFstD.comp
    (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hM))
  have hJ : PolyTimeComputable fun w => List.replicate (J w) true :=
    EncodingMachines.unaryLength_poly (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp
        (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hM))))
  have hPW : PolyTimeComputable PW := polyTimeComputable_pairSndD.comp
    (polyTimeComputable_pairSndD.comp
      (polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp hM)))
  have hH : PolyTimeComputable fun w => Strategy.encodeMsgs (BinArith.decWords (PW w)) :=
    (polyTimeComputable_encWords_decWords hPW).congr
      (fun _ => (encodeMsgs_eq_encWords _).symm)
  have hRaw : PolyTimeComputable Raw :=
    polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  let F : List Bool → List Bool := fun w => phaseContinuation S k B Q verifierFirst
    (X w) (Z w) (RV w) (J w) (BinArith.decWords (PW w)) (Raw w) (NUPPT.inCoins w)
  have hF : PolyTimeComputable F := phaseContinuation_poly S hS k B Q verifierFirst
    hX hZ hRV hRaw NUPPT.polyTimeComputable_inCoins hJ hH
  -- The published uniform constructor and layout readers give the exact activation.
  refine ⟨NUPPT.ofPolyTimeUniform hF (.mul Q S.coins),
    NUPPT.ofPolyTimeUniform_uniform hF _, NUPPT.coins_ofPolyTimeUniform hF _, ?_⟩
  intro n raw x z rV j preWord r
  rw [NUPPT.runAtL_ofPolyTimeUniform, NUPPT.advInput_eq, ← NUPPT.layout_eq]
  dsimp only [F, X, Z, RV, J, PW, Raw, M]
  simp only [NUPPT.inArg_layout, NUPPT.inCoins_layout, reductionData_eq,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]

/-- Given uniform `S`, distinguisher `D`, polynomials `k,B,Q`, orientation `verifierFirst`,
metadata families `X,Z,RV,J,PreWord`, and a polynomial bound on their packed `reductionData`,
there is a nonuniform reduction with coins `Q*S.coins + D.coins`. Its activation normalizes
the current raw phase, simulates the suffix on the first `Q*S.coins` bits, and runs `D` on
the final canonical view with the remaining coins. No witness is stored or tested.
[PS10, Theorem 175.1; Gol01, §4.3.4, advised one-phase hybrid reduction].
`∃ Red : NUPPT, Red.coins = .add (.mul Q S.coins) D.coins ∧ ∀ (n : ℕ) (raw r : List Bool),
Red.runAtL n raw r = D.runAtL n (phaseContinuation S k B Q verifierFirst (X n) (Z n) (RV n) (J n)
(BinArith.decWords (PreWord n)) raw (r.take …`.

**Proof sketch.** Take the uniform continuation sampler. Precompose `D` with the second pair
projection, then apply the published fresh-coin sequential composition so that `D` receives
only the sampled final view. Apply the ordinary bounded-advice closure to the packed metadata
family. The three published activation equations, the sampler's exact reader, and its coin
polynomial identify the complete reduction without constructing a new machine or host. -/
theorem exists_phaseReduction (S : NUPPT) (hS : S.Uniform) (D : NUPPT)
    (k B Q : PolyExpr) (verifierFirst : Bool) (X Z RV : ℕ → List Bool)
    (J : ℕ → ℕ) (PreWord : ℕ → List Bool) (b : PolyExpr)
    (hdata : ∀ n, (reductionData (X n) (Z n) (RV n) (J n) (PreWord n)).length ≤ b.eval n) :
    ∃ Red : NUPPT, Red.coins = .add (.mul Q S.coins) D.coins ∧
      ∀ (n : ℕ) (raw r : List Bool), Red.runAtL n raw r =
        D.runAtL n
          (phaseContinuation S k B Q verifierFirst (X n) (Z n) (RV n) (J n)
            (BinArith.decWords (PreWord n)) raw (r.take ((PolyExpr.mul Q S.coins).eval n)))
          (r.drop ((PolyExpr.mul Q S.coins).eval n)) := by
  obtain ⟨U, _, hUc, hU⟩ := exists_continuationSampler S hS k B Q verifierFirst
  obtain ⟨D0, hD0c, _, _, hD0⟩ := NUPPT.exists_comp D
    (pre := pairSndD) (post := fun w => w) polyTimeComputable_pairSndD polyTimeComputable_id
  obtain ⟨C, hCc, _, hC⟩ := NUPPT.exists_seq U D0
  let β : ℕ → List Bool := fun n => reductionData (X n) (Z n) (RV n) (J n) (PreWord n)
  have hβ : ∀ n, (β n).length ≤ b.eval n := hdata
  obtain ⟨Red, hRc, hR⟩ := NUPPT.exists_withAdvice C β b hβ
  refine ⟨Red, ?_, ?_⟩
  · rw [hRc, hCc, hUc, hD0c]
  · intro n raw r
    rw [hR, hC, hD0, pairSndD_pairEncode]
    dsimp only [β]
    rw [hU]
    simp only [NUPPT.coinLen_eq, hUc]

end TCSlib.Cryptography.SequentialZK
