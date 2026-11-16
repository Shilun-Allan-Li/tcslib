/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.SimulatorMachine

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Polynomial-time normalized suffix simulation

A simulated suffix starts from an arbitrary message prefix and phase index. The initial
messages are preserved, and each further phase adds only bounded normalized messages and
empty fillers. The semantic recursion is realized by the existing published counted-loop
host; no new control host or hand-built machine is introduced. All word inputs are total,
including malformed prefix encodings and phase indices beyond the supplied random tape.

## Main definitions

* `phaseStep`: one normalized phase appended to an arbitrary prefix.
* `phaseSuffix`: a specified number of normalized phases after an arbitrary starting phase.

## Main results

* `length_encodeMsgs_phaseStep_le`, `length_encodeMsgs_phaseSuffix_le`: additive growth bounds.
* `phaseStep_poly`, `phaseSuffix_poly`: polynomial-time normalized step and suffix.
* `phaseSuffix_raw_poly`: total polynomial-time suffix from a decoded arbitrary prefix word.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- For simulator `S`, bounds `k,B`, orientation `verifierFirst`, input/auxiliary words `x,z`,
fixed verifier tape `rV`, phase-tape source `rS`, phase `j`, and earlier prefix `pre`,
`phaseStep` appends the normalized `S` output at `phaseAux z rV j pre` and `k(|x|)-p` empty
fillers, with `p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`.
The simulator uses global coin block `j`. [PS10, Theorem 175.1, simulated suffix update]. -/
def phaseStep (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (j : ℕ) (pre : List (List Bool)) : List (List Bool) :=
  let aux := phaseAux z rV j pre
  let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
  pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
    (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)) ++
      List.replicate (k.eval x.length - p) [])

/-- The equation for `phaseStep S k B verifierFirst x z rV rS j pre` is the earlier prefix
followed by normalized real messages from simulator coin block `j` and then empty fillers.
`phaseStep S k B verifierFirst x z rV rS j pre = let aux := phaseAux z rV j pre; let p := if
verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2; pre ++ (normalizePhaseMsgs x
aux p (B.eval x.length) (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS))
++ List.replicate (k.eval x.length - p) [])`. -/
theorem phaseStep_eq (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (j : ℕ) (pre : List (List Bool)) :
    phaseStep S k B verifierFirst x z rV rS j pre =
      let aux := phaseAux z rV j pre
      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
      pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
        (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)) ++
          List.replicate (k.eval x.length - p) []) := rfl

/-- One normalized step increases the encoded prefix length by at most
`k(|x|) * (2*B(|x|)+2)`, regardless of the earlier messages or simulator output.
`(Strategy.encodeMsgs (phaseStep S k B verifierFirst x z rV rS j pre)).length ≤ (Strategy.encodeMsgs
pre).length + k.eval x.length * (2 * B.eval x.length + 2)`.

**Proof sketch.** The normalized real portion has `p` messages of at most `B` bits and the
remaining `k-p` messages are empty. Their encoding lengths are bounded by `p(2B+2)` and
`(k-p)(2B+2)`, whose sum is `k(2B+2)` because `p≤k`. The public encoding-append equation
adds this bound to the unchanged initial encoding length. -/
theorem length_encodeMsgs_phaseStep_le (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (j : ℕ) (pre : List (List Bool)) :
    (Strategy.encodeMsgs (phaseStep S k B verifierFirst x z rV rS j pre)).length ≤
      (Strategy.encodeMsgs pre).length + k.eval x.length * (2 * B.eval x.length + 2) := by
  let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
  let aux := phaseAux z rV j pre
  let raw := S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)
  have hreal := length_encodeMsgs_normalizePhaseMsgs_le x aux p (B.eval x.length) raw
  have hfill := CommitmentLemmas.length_encodeMsgs_le
    (List.replicate (k.eval x.length - p) ([] : List Bool)) (B.eval x.length)
    (fun m hm => by
      have he := (List.mem_replicate.mp hm).2
      subst m
      exact Nat.zero_le _)
  rw [List.length_replicate] at hfill
  have hp : p ≤ k.eval x.length := by
    dsimp only [p]
    cases verifierFirst <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega
  have hpk : p + (k.eval x.length - p) = k.eval x.length := by omega
  have hsum : p * (2 * B.eval x.length + 2) +
      (k.eval x.length - p) * (2 * B.eval x.length + 2) =
        k.eval x.length * (2 * B.eval x.length + 2) := by rw [← Nat.add_mul, hpk]
  simp only [phaseStep_eq, CommitmentLemmas.encodeMsgs_append, List.length_append]
  dsimp only [p, aux, raw] at hreal hfill hsum
  omega

/-- For uniform `S`, fixed `k,B,verifierFirst`, polynomial-time words `X,Z,RV,RS`, a unary
polynomial-time phase `J`, and a message family `H` with polynomial-time encoding, the
normalized update is polynomial-time: `w ↦ encodeMsgs (phaseStep S k B verifierFirst
(X w) (Z w) (RV w) (RS w) (J w) (H w))`. No message bound on `H` is required.
[PS10, Theorem 175.1, simulated-suffix step].
`PolyTimeComputable fun w => Strategy.encodeMsgs (phaseStep S k B verifierFirst (X w) (Z w) (RV w)
(RS w) (J w) (H w))`.

**Proof sketch.** Assemble the phase auxiliary word from the input functions and encoded
prefix, cut out global simulator coin block `J`, and run the original uniform simulator's
polynomial-time output. Apply the published canonical phase normalizer. Unary arithmetic
computes the real/filler slot counts; the existing counted emitter encodes the empty fillers.
Concatenate the unchanged input encoding and both new encodings using the public append
reader. This is a polynomial-time leaf, with no iteration host construction. -/
theorem phaseStep_poly (S : NUPPT) (hS : S.Uniform) (k B : PolyExpr)
    (verifierFirst : Bool) {X Z RV RS : List Bool → List Bool} {J : List Bool → ℕ}
    {H : List Bool → List (List Bool)}
    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS)
    (hJ : PolyTimeComputable fun w => List.replicate (J w) true)
    (hH : PolyTimeComputable fun w => Strategy.encodeMsgs (H w)) :
    PolyTimeComputable fun w => Strategy.encodeMsgs
      (phaseStep S k B verifierFirst (X w) (Z w) (RV w) (RS w) (J w) (H w)) := by
  -- Assemble the known phase metadata, tape slice and one uniform simulator call.
  have haux := phaseAux_poly hZ hRV hJ hH
  have hcoins : PolyTimeComputable fun w =>
      coinBlock (S.coinLen (X w).length) (J w) (RS w) := by
    simpa only [NUPPT.coinLen_eq, List.length_replicate] using
      GI.coinSlice_poly S.coins hX hJ hRS
  have hlay := NUPPT.polyTimeComputable_layout (EncodingMachines.unaryLength_poly hX)
    (hX.pairEncode haux) (polyTimeComputable_const []) hcoins
  have hsim : PolyTimeComputable fun w =>
      S.runAtL (X w).length (pairEncode (X w) (phaseAux (Z w) (RV w) (J w) (H w)))
        (coinBlock (S.coinLen (X w).length) (J w) (RS w)) := by
    refine (S.polyTimeComputable_output.comp hlay).congr fun w => ?_
    rw [Function.comp_apply, NUPPT.runAtL_eq_output_layout, hS.advice_eq]
  -- The canonical normalizer and empty-filler emitter provide the new message encoding.
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
  have hnorm := polyTimeComputable_encode_normalizePhaseMsgs hX haux hsim hP hbits
  have hfill := encode_emptyMsgs_poly (EncodingMachines.unarySub_poly hK hP)
  refine (hH.append (hnorm.append hfill)).congr fun w => ?_
  rw [phaseStep_eq, CommitmentLemmas.encodeMsgs_append, CommitmentLemmas.encodeMsgs_append]

/-- Starting from `pre0` at phase `start`, `phaseSuffix S k B verifierFirst x z rV rS start
pre0 t` applies the normalized append update at phases `start, …, start+t-1`, reading those
global coin blocks from `rS`. It is a mathematical sequence realized below by the existing
published counted-loop host. [PS10, Theorem 175.1, normalized simulated suffix].
`phaseSuffix S k B verifierFirst x z rV rS start pre0 t = match t with | 0 => pre0 | i + 1 =>
phaseStep S k B verifierFirst x z rV rS (start + i) (phaseSuffix S k B verifierFirst x z rV rS start
pre0 i)`. -/
def phaseSuffix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) : ℕ → List (List Bool)
  | 0 => pre0
  | i + 1 => phaseStep S k B verifierFirst x z rV rS (start + i)
      (phaseSuffix S k B verifierFirst x z rV rS start pre0 i)

/-- At zero suffix phases, `phaseSuffix S k B verifierFirst x z rV rS start pre0 0 = pre0`. -/
theorem phaseSuffix_zero (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) :
    phaseSuffix S k B verifierFirst x z rV rS start pre0 0 = pre0 := rfl

/-- Suffix phase `i+1` applies `phaseStep` at global index `start+i` to the prefix after `i`
steps: `phaseSuffix … (i+1) = phaseStep … (start+i) (phaseSuffix … i)`. -/
theorem phaseSuffix_succ (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) (i : ℕ) :
    phaseSuffix S k B verifierFirst x z rV rS start pre0 (i + 1) =
      phaseStep S k B verifierFirst x z rV rS (start + i)
        (phaseSuffix S k B verifierFirst x z rV rS start pre0 i) := rfl

/-- The exhaustive suffix equation returns `pre0` at zero and, at `i+1`, applies
`phaseStep` at global index `start+i` to `phaseSuffix … i`.
`phaseSuffix S k B verifierFirst x z rV rS start pre0 t = match t with | 0 => pre0 | i + 1 =>
phaseStep S k B verifierFirst x z rV rS (start + i) (phaseSuffix S k B verifierFirst x z rV rS start
pre0 i)`. -/
theorem phaseSuffix_eq (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) (t : ℕ) :
    phaseSuffix S k B verifierFirst x z rV rS start pre0 t =
      match t with
      | 0 => pre0
      | i + 1 => phaseStep S k B verifierFirst x z rV rS (start + i)
          (phaseSuffix S k B verifierFirst x z rV rS start pre0 i) :=
  match t with
  | 0 => phaseSuffix_zero S k B verifierFirst x z rV rS start pre0
  | i + 1 => phaseSuffix_succ S k B verifierFirst x z rV rS start pre0 i

/-- For any initial prefix `pre0`, the suffix encoding grows by at most
`t * k(|x|) * (2*B(|x|)+2)` beyond its initial encoded length. No bound is required on
individual initial messages or on the starting phase index.
`(Strategy.encodeMsgs (phaseSuffix S k B verifierFirst x z rV rS start pre0 t)).length ≤
(Strategy.encodeMsgs pre0).length + t * k.eval x.length * (2 * B.eval x.length + 2)`. -/
theorem length_encodeMsgs_phaseSuffix_le (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (start : ℕ) (pre0 : List (List Bool)) (t : ℕ) :
    (Strategy.encodeMsgs (phaseSuffix S k B verifierFirst x z rV rS start pre0 t)).length ≤
      (Strategy.encodeMsgs pre0).length + t * k.eval x.length * (2 * B.eval x.length + 2) := by
  induction t with
  | zero => rw [phaseSuffix_zero, Nat.zero_mul, Nat.zero_mul, Nat.add_zero]
  | succ t ih =>
    rw [phaseSuffix_succ]
    have hstep := length_encodeMsgs_phaseStep_le S k B verifierFirst x z rV rS (start + t)
      (phaseSuffix S k B verifierFirst x z rV rS start pre0 t)
    rw [Nat.succ_mul, Nat.add_mul]
    omega

/-- For uniform `S`, fixed `k,B,verifierFirst`, polynomial-time words `X,Z,RV,RS`, unary
polynomial-time starting phase/count `Start,Count`, and initial message family `H` with
polynomial-time encoding, the entire suffix encoding is polynomial-time. There is no range
premise on `Start,Count` and no bound on individual messages of `H`.
[PS10, Theorem 175.1; Gol01, §4.3.4, efficient simulated suffix].
`PolyTimeComputable fun w => Strategy.encodeMsgs (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w)
(RS w) (Start w) (H w) (Count w))`.

**Proof sketch.** Use the published counted-loop host with encoded-prefix state and its
existing unary counter `i`. The update is the polynomial-time leaf `phaseStep_poly`, at index
`Start+i`, after canonically decoding the reached state. Induction identifies the state with
the semantic suffix. Its additive encoding bound, together with polynomial output-length
bounds for the initial encoding, unary count and common input, gives the existing host's
polynomial orbit envelope. No new host or control machine is constructed. -/
theorem phaseSuffix_poly (S : NUPPT) (hS : S.Uniform) (k B : PolyExpr)
    (verifierFirst : Bool) {X Z RV RS : List Bool → List Bool}
    {Start Count : List Bool → ℕ} {H : List Bool → List (List Bool)}
    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS)
    (hStart : PolyTimeComputable fun w => List.replicate (Start w) true)
    (hCount : PolyTimeComputable fun w => List.replicate (Count w) true)
    (hH : PolyTimeComputable fun w => Strategy.encodeMsgs (H w)) :
    PolyTimeComputable fun w => Strategy.encodeMsgs
      (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Start w) (H w) (Count w)) := by
  let upd : List Bool → List Bool := fun w => Strategy.encodeMsgs
    (phaseStep S k B verifierFirst (X (pairFstD w)) (Z (pairFstD w))
      (RV (pairFstD w)) (RS (pairFstD w))
      (Start (pairFstD w) + (pairFstD (pairSndD w)).length)
      (BinArith.decWords (pairSndD (pairSndD w))))
  -- Instantiate the new leaf with the existing loop's input, counter and state projections.
  have hXt : PolyTimeComputable fun w => X (pairFstD w) := hX.comp polyTimeComputable_pairFstD
  have hZt : PolyTimeComputable fun w => Z (pairFstD w) := hZ.comp polyTimeComputable_pairFstD
  have hRVt : PolyTimeComputable fun w => RV (pairFstD w) := hRV.comp polyTimeComputable_pairFstD
  have hRSt : PolyTimeComputable fun w => RS (pairFstD w) := hRS.comp polyTimeComputable_pairFstD
  have hJ := EncodingMachines.unaryAdd_poly (hStart.comp polyTimeComputable_pairFstD)
    (EncodingMachines.unaryLength_poly
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD))
  have hcanonical := polyTimeComputable_encWords_decWords
    (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD)
  have hpre : PolyTimeComputable fun w =>
      Strategy.encodeMsgs (BinArith.decWords (pairSndD (pairSndD w))) :=
    hcanonical.congr fun w => (encodeMsgs_eq_encWords _).symm
  have hupd : PolyTimeComputable upd :=
    phaseStep_poly S hS k B verifierFirst hXt hZt hRVt hRSt hJ hpre
  -- Every actual state is the canonical encoding of the mathematical suffix prefix.
  have hclosed : ∀ w i,
      EncodingMachines.loopState upd (fun w => Strategy.encodeMsgs (H w)) w i =
        Strategy.encodeMsgs (phaseSuffix S k B verifierFirst
          (X w) (Z w) (RV w) (RS w) (Start w) (H w) i) := by
    intro w i
    induction i with
    | zero => rw [EncodingMachines.loopState_zero, phaseSuffix_zero]
    | succ i ih =>
      rw [EncodingMachines.loopState_succ]
      dsimp only [upd]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      rw [ih]
      have hdec : BinArith.decWords (Strategy.encodeMsgs
          (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Start w) (H w) i)) =
          phaseSuffix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Start w) (H w) i :=
        (congrArg BinArith.decWords (encodeMsgs_eq_encWords _)).trans
          (BinArith.decWords_encWords _)
      rw [hdec, phaseSuffix_succ]
  -- Add the initial encoding's polynomial size to the normalized suffix-growth envelope.
  obtain ⟨CX, dX, hCX⟩ := hX.output_length_le
  obtain ⟨CN, dN, hCN⟩ := hCount.output_length_le
  obtain ⟨CH, dH, hCH⟩ := hH.output_length_le
  let XP : PolyExpr := .normal CX dX
  let bound : PolyExpr := .add (.normal CH dH)
    (.mul (.mul (.normal CN dN) (k.subst XP))
      (.add (.mul (.const 2) (B.subst XP)) (.const 2)))
  have hloop := ColMachines.polyTimeComputable_loopState' hupd hH hCount bound
    (fun w i hi => by
      rw [hclosed]
      have hx : (X w).length ≤ XP.eval w.length := by
        simpa only [XP, PolyExpr.eval_normal] using hCX w
      have hi' : i ≤ CN * (w.length + 1) ^ dN :=
        hi.trans (by simpa only [List.length_replicate] using hCN w)
      have hk := k.eval_mono hx
      have hb := B.eval_mono hx
      simp only [bound, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const,
        PolyExpr.eval_normal, PolyExpr.eval_subst]
      calc
        _ ≤ (Strategy.encodeMsgs (H w)).length +
            i * k.eval (X w).length * (2 * B.eval (X w).length + 2) :=
          length_encodeMsgs_phaseSuffix_le S k B verifierFirst
            (X w) (Z w) (RV w) (RS w) (Start w) (H w) i
        _ ≤ CH * (w.length + 1) ^ dH + CN * (w.length + 1) ^ dN *
            k.eval (XP.eval w.length) * (2 * B.eval (XP.eval w.length) + 2) :=
          Nat.add_le_add (hCH w) (Nat.mul_le_mul (Nat.mul_le_mul hi' hk) (by omega)))
  exact hloop.congr fun w => hclosed w _

/-- For uniform `S`, fixed `k,B,verifierFirst`, polynomial-time words `X,Z,RV,RS,Raw`, and
unary polynomial-time `Start,Count`, decode the arbitrary word `Raw w` as the initial prefix.
The resulting suffix encoding is polynomial-time on every input, including malformed words
and phase indices beyond the available tape.
`PolyTimeComputable fun w => Strategy.encodeMsgs (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w)
(RS w) (Start w) (BinArith.decWords (Raw w)) (Count w))`. -/
theorem phaseSuffix_raw_poly (S : NUPPT) (hS : S.Uniform) (k B : PolyExpr)
    (verifierFirst : Bool) {X Z RV RS Raw : List Bool → List Bool}
    {Start Count : List Bool → ℕ}
    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS)
    (hRaw : PolyTimeComputable Raw)
    (hStart : PolyTimeComputable fun w => List.replicate (Start w) true)
    (hCount : PolyTimeComputable fun w => List.replicate (Count w) true) :
    PolyTimeComputable fun w => Strategy.encodeMsgs
      (phaseSuffix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Start w)
        (BinArith.decWords (Raw w)) (Count w)) :=
  phaseSuffix_poly S hS k B verifierFirst hX hZ hRV hRS hStart hCount
    ((polyTimeComputable_encWords_decWords hRaw).congr
      (fun _ => (encodeMsgs_eq_encWords _).symm))

/-- Starting at phase zero with empty prefix gives the whole-prefix semantics:
`phaseSuffix S k B verifierFirst x z rV rS 0 [] t =
phasePrefix S k B verifierFirst x z rV rS t`. -/
theorem phaseSuffix_zero_nil (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (t : ℕ) :
    phaseSuffix S k B verifierFirst x z rV rS 0 [] t =
      phasePrefix S k B verifierFirst x z rV rS t := by
  induction t with
  | zero => rw [phaseSuffix_zero, phasePrefix_zero]
  | succ t ih =>
    rw [phaseSuffix_succ, ih, Nat.zero_add, phaseStep_eq, phasePrefix_succ]

end TCSlib.Cryptography.SequentialZK
