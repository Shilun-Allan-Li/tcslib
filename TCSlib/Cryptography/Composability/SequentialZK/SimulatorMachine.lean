/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Composability.SequentialZK.PhaseView
import TCSlib.Cryptography.Composability.SequentialZK.WrappedVerifier
import TCSlib.Cryptography.ZeroKnowledge.Defs
import TCSlib.Cryptography.ZeroKnowledge.GraphIsomorphism.EfficiencyRep

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The strict polynomial-time sequential phase simulator

A single verifier tape and independent blocks of the phase simulator's tape drive a sequence
of canonical bounded phase normalizations. The semantic recursion `phasePrefix` specifies
that sequence. Its machine implementation instantiates the published counted-loop host
`ColMachines.polyTimeComputable_loopState'`; it introduces no new control host or machine.

## Main definitions

* `phasePrefix`: the normalized received-prover prefix after a specified number of phases.

## Main results

* `phasePrefix_eq`, `phasePrefix_zero`, `phasePrefix_succ`: exact semantic readers.
* `length_phasePrefix`, `length_le_of_mem_phasePrefix`, `length_encodeMsgs_phasePrefix_le`:
  exact slot count and uniform message/encoding bounds.
* `phasePrefix_poly`: polynomial-time assembly of the entire normalized prefix.
* `exists_phaseSimulator`: a uniform simulator with one verifier tape and fresh phase tapes.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.2.1, Theorem 175.1.
* [Gol01] O. Goldreich, *Foundations of Cryptography, Volume I: Basic Tools*, Cambridge
  University Press, 2001, §4.3.4.
-/

namespace TCSlib.Cryptography.SequentialZK

open Complexity Turing

/-- The normalized prefix after `i` phases uses simulator `S`, round/bit bounds `k,B`,
orientation `verifierFirst`, input/auxiliary words `x,z`, one verifier tape `rV`, and phase-tape
source `rS`. Each phase calls `S` on `phaseAux z rV i pre`, retains exactly
`p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2` bounded real messages, and appends
`k(|x|)-p` empty fillers. [PS10, Theorem 175.1, the sequential simulator].

This recursion is the public mathematical specification; its polynomial-time realization
below is an instance of the existing counted-loop host, rather than a new control host. -/
def phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) : ℕ → List (List Bool)
  | 0 => []
  | i + 1 =>
    let pre := phasePrefix S k B verifierFirst x z rV rS i
    let aux := phaseAux z rV i pre
    let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
    pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
      (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) i rS)) ++
        List.replicate (k.eval x.length - p) [])

/-- Before any phase, `phasePrefix S k B verifierFirst x z rV rS 0 = []`. -/
theorem phasePrefix_zero (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) : phasePrefix S k B verifierFirst x z rV rS 0 = [] := rfl

/-- Phase `i+1` extends `pre = phasePrefix S k B verifierFirst x z rV rS i` with the normalized
output of `S.runAtL |x| (pairEncode x (phaseAux z rV i pre))` on coin block `i`, then the
`k(|x|)-p` empty fillers, for `p = if verifierFirst then k(|x|)/2 else (k(|x|)+1)/2`. -/
theorem phasePrefix_succ (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) :
    phasePrefix S k B verifierFirst x z rV rS (i + 1) =
      let pre := phasePrefix S k B verifierFirst x z rV rS i
      let aux := phaseAux z rV i pre
      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
      pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
        (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) i rS)) ++
          List.replicate (k.eval x.length - p) []) := rfl

/-- The exhaustive equation for `phasePrefix … i` is `[]` at zero; at `j+1`, with
`pre = phasePrefix … j`, it appends the canonical normalized `S.runAtL` output at
`phaseAux z rV j pre` on coin block `j`, followed by the `k(|x|)-p` empty fillers. -/
theorem phasePrefix_eq (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) :
    phasePrefix S k B verifierFirst x z rV rS i =
      match i with
      | 0 => []
      | j + 1 =>
        let pre := phasePrefix S k B verifierFirst x z rV rS j
        let aux := phaseAux z rV j pre
        let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
        pre ++ (normalizePhaseMsgs x aux p (B.eval x.length)
          (S.runAtL x.length (pairEncode x aux) (coinBlock (S.coinLen x.length) j rS)) ++
            List.replicate (k.eval x.length - p) []) :=
  match i with
  | 0 => phasePrefix_zero S k B verifierFirst x z rV rS
  | j + 1 => phasePrefix_succ S k B verifierFirst x z rV rS j

/-- If phase coin block `i` equals `List.ofFn r`, phase `i+1` calls precisely
`S.simulate x (phaseAux z rV i pre) r`, with `pre` the earlier phase prefix.
`phasePrefix S k B verifierFirst x z rV rS (i + 1) = let pre := phasePrefix S k B verifierFirst x z
rV rS i; let aux := phaseAux z rV i pre; let p := if verifierFirst then k.eval x.length / 2 else
(k.eval x.length + 1) / 2; pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) (S.simulate x aux r)
++ List.replicate (k.eval x.length - p) [])`. -/
theorem phasePrefix_succ_simulate (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) (r : S.Coins x.length)
    (hcoins : coinBlock (S.coinLen x.length) i rS = List.ofFn r) :
    phasePrefix S k B verifierFirst x z rV rS (i + 1) =
      let pre := phasePrefix S k B verifierFirst x z rV rS i
      let aux := phaseAux z rV i pre
      let p := if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2
      pre ++ (normalizePhaseMsgs x aux p (B.eval x.length) (S.simulate x aux r) ++
        List.replicate (k.eval x.length - p) []) := by
  rw [phasePrefix_succ]
  dsimp only
  rw [hcoins, ← NUPPT.runAt_eq, ← NUPPT.simulate_eq]

/-- After `i` phases the normalized prefix has exactly `i * k(|x|)` messages:
`(phasePrefix S k B verifierFirst x z rV rS i).length = i * k.eval x.length`. -/
theorem length_phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) :
    (phasePrefix S k B verifierFirst x z rV rS i).length = i * k.eval x.length := by
  induction i with
  | zero => rw [phasePrefix_zero, List.length_nil, Nat.zero_mul]
  | succ i ih =>
    rw [phasePrefix_succ]
    dsimp only
    rw [List.length_append, List.length_append, length_normalizePhaseMsgs,
      List.length_replicate, ih, Nat.succ_mul]
    have hp : (if verifierFirst then k.eval x.length / 2 else (k.eval x.length + 1) / 2) ≤
        k.eval x.length := by cases verifierFirst <;> simp only [Bool.false_eq_true,
          if_false, if_true] <;> omega
    omega

/-- Every message in `phasePrefix S k B verifierFirst x z rV rS i` has at most `B(|x|)` bits.
`m.length ≤ B.eval x.length`.

**Proof sketch.** Induct on the number of phases. Earlier messages satisfy the induction
hypothesis, normalized real messages satisfy the published bit bound, and every filler is
empty. These are exactly the three portions of the next prefix. -/
theorem length_le_of_mem_phasePrefix (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) {m : List Bool}
    (hm : m ∈ phasePrefix S k B verifierFirst x z rV rS i) : m.length ≤ B.eval x.length := by
  induction i generalizing m with
  | zero =>
    rw [phasePrefix_zero] at hm
    exact False.elim (List.not_mem_nil hm)
  | succ i ih =>
    rw [phasePrefix_succ] at hm
    dsimp only at hm
    rcases List.mem_append.mp hm with hm | hm
    · exact ih hm
    · rcases List.mem_append.mp hm with hm | hm
      · exact length_le_of_mem_normalizePhaseMsgs _ _ _ _ _ hm
      · have he := (List.mem_replicate.mp hm).2
        subst m
        exact Nat.zero_le _

/-- The encoded prefix after `i` phases has length at most
`i * k(|x|) * (2 * B(|x|) + 2)`, uniformly over every simulator output and tape.
`(Strategy.encodeMsgs (phasePrefix S k B verifierFirst x z rV rS i)).length ≤ i * k.eval x.length *
(2 * B.eval x.length + 2)`. -/
theorem length_encodeMsgs_phasePrefix_le (S : NUPPT) (k B : PolyExpr) (verifierFirst : Bool)
    (x z rV rS : List Bool) (i : ℕ) :
    (Strategy.encodeMsgs (phasePrefix S k B verifierFirst x z rV rS i)).length ≤
      i * k.eval x.length * (2 * B.eval x.length + 2) := by
  have h := CommitmentLemmas.length_encodeMsgs_le
    (phasePrefix S k B verifierFirst x z rV rS i) (B.eval x.length)
    (fun m hm => length_le_of_mem_phasePrefix S k B verifierFirst x z rV rS i hm)
  simpa only [length_phasePrefix] using h

/-- If `N` is polynomial-time in unary, the encoding of `N w` empty messages is
polynomial-time: `w ↦ Strategy.encodeMsgs (List.replicate (N w) [])`.
`PolyTimeComputable fun w => Strategy.encodeMsgs (List.replicate (N w) [])`. -/
theorem encode_emptyMsgs_poly {N : List Bool → ℕ}
    (hN : PolyTimeComputable fun w => List.replicate (N w) true) :
    PolyTimeComputable fun w => Strategy.encodeMsgs (List.replicate (N w) []) := by
  have h := ColMachines.polyTimeComputable_flatMap_range
    (E := fun _ _ => pairEncode ([] : List Bool) [])
    (polyTimeComputable_const (pairEncode ([] : List Bool) [])) hN
  refine h.congr fun w => ?_
  have he : List.replicate (N w) ([] : List Bool) =
      (List.range (N w)).map (fun _ => []) := by
    rw [List.map_const', List.length_range]
  rw [ColMachines.encodeMsgs_eq_flatMap, he, List.flatMap_map]

/-- For a uniform `S`, fixed polynomials `k,B,Q`, orientation `verifierFirst`, and
polynomial-time words `X,Z,RV,RS`, the entire encoded prefix is polynomial-time:
`w ↦ encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w)
(Q.eval (X w).length))`. [PS10, Theorem 175.1, strict-PPT sequential simulation].
`PolyTimeComputable fun w => Strategy.encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w)
(RS w) (Q.eval (X w).length))`.

**Proof sketch.** Instantiate the published counted-loop host with the encoded prefix as
state and its existing unary counter as phase index. The step decodes the prior state,
assembles the phase auxiliary input, runs `S` on the selected fresh coin block, canonically
normalizes its output, and appends that phase's real-message encoding and empty fillers.
The state is exactly the encoding of the semantic prefix, by induction using the published
loop equations. Its encoding bound, together with a polynomial bound on `|X w|`, bounds every
genuine orbit state. The existing orbit-bounded counted-loop theorem then gives strict
polynomial time, with no newly constructed host. -/
theorem phasePrefix_poly (S : NUPPT) (hS : S.Uniform) (k B Q : PolyExpr)
    (verifierFirst : Bool) {X Z RV RS : List Bool → List Bool}
    (hX : PolyTimeComputable X) (hZ : PolyTimeComputable Z)
    (hRV : PolyTimeComputable RV) (hRS : PolyTimeComputable RS) :
    PolyTimeComputable fun w => Strategy.encodeMsgs
      (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Q.eval (X w).length)) := by
  let upd : List Bool → List Bool := fun w =>
    let t := pairFstD w
    let i := (pairFstD (pairSndD w)).length
    let pre := BinArith.decWords (pairSndD (pairSndD w))
    let aux := phaseAux (Z t) (RV t) i pre
    let p := if verifierFirst then k.eval (X t).length / 2 else (k.eval (X t).length + 1) / 2
    pairSndD (pairSndD w) ++
      (Strategy.encodeMsgs (normalizePhaseMsgs (X t) aux p (B.eval (X t).length)
        (S.runAtL (X t).length (pairEncode (X t) aux)
          (coinBlock (S.coinLen (X t).length) i (RS t)))) ++
        Strategy.encodeMsgs (List.replicate (k.eval (X t).length - p) []))
  -- Every component of one update is assembled from published polynomial-time machines.
  have hXt : PolyTimeComputable fun w => X (pairFstD w) := hX.comp polyTimeComputable_pairFstD
  have hZt : PolyTimeComputable fun w => Z (pairFstD w) := hZ.comp polyTimeComputable_pairFstD
  have hRVt : PolyTimeComputable fun w => RV (pairFstD w) := hRV.comp polyTimeComputable_pairFstD
  have hRSt : PolyTimeComputable fun w => RS (pairFstD w) := hRS.comp polyTimeComputable_pairFstD
  have hIword := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  have hI := EncodingMachines.unaryLength_poly hIword
  have hstate := polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD
  have hcanonical := polyTimeComputable_encWords_decWords hstate
  have hpre : PolyTimeComputable fun w =>
      Strategy.encodeMsgs (BinArith.decWords (pairSndD (pairSndD w))) :=
    hcanonical.congr fun w => (encodeMsgs_eq_encWords _).symm
  have haux := phaseAux_poly hZt hRVt hI hpre
  have hcoins : PolyTimeComputable fun w =>
      coinBlock (S.coinLen (X (pairFstD w)).length) (pairFstD (pairSndD w)).length
        (RS (pairFstD w)) := by
    simpa only [NUPPT.coinLen_eq] using GI.coinSlice_poly S.coins hXt hIword hRSt
  have hlay := NUPPT.polyTimeComputable_layout (EncodingMachines.unaryLength_poly hXt)
    (hXt.pairEncode haux) (polyTimeComputable_const []) hcoins
  have hsim : PolyTimeComputable fun w =>
      S.runAtL (X (pairFstD w)).length
        (pairEncode (X (pairFstD w)) (phaseAux (Z (pairFstD w)) (RV (pairFstD w))
          (pairFstD (pairSndD w)).length (BinArith.decWords (pairSndD (pairSndD w)))))
        (coinBlock (S.coinLen (X (pairFstD w)).length) (pairFstD (pairSndD w)).length
          (RS (pairFstD w))) := by
    refine (S.polyTimeComputable_output.comp hlay).congr fun w => ?_
    rw [Function.comp_apply, NUPPT.runAtL_eq_output_layout, hS.advice_eq]
    simp only [Function.comp_apply]
  have hK := EncodingMachines.unaryPolyOf_poly k (EncodingMachines.unaryLength_poly hXt)
  have hP : PolyTimeComputable fun w => List.replicate
      (if verifierFirst then k.eval (X (pairFstD w)).length / 2
        else (k.eval (X (pairFstD w)).length + 1) / 2) true := by
    cases verifierFirst
    · simpa only [EncodingMachines.divNum_eq] using EncodingMachines.divNum_poly
        (EncodingMachines.unaryAdd_poly hK (EncodingMachines.unaryConst_poly 1))
        (EncodingMachines.unaryConst_poly 2)
    · simpa only [EncodingMachines.divNum_eq] using
        EncodingMachines.divNum_poly hK (EncodingMachines.unaryConst_poly 2)
  have hbits := EncodingMachines.unaryPolyOf_poly B (EncodingMachines.unaryLength_poly hXt)
  have hnorm := polyTimeComputable_encode_normalizePhaseMsgs hXt haux hsim hP hbits
  have hfill := encode_emptyMsgs_poly (EncodingMachines.unarySub_poly hK hP)
  have hupd : PolyTimeComputable upd := hstate.append (hnorm.append hfill)
  -- The machine state is exactly the public semantic prefix on the genuine orbit.
  have hclosed : ∀ w i, EncodingMachines.loopState upd (fun _ => []) w i =
      Strategy.encodeMsgs (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i) := by
    intro w i
    induction i with
    | zero => rw [EncodingMachines.loopState_zero, phasePrefix_zero, Strategy.encodeMsgs_nil]
    | succ i ih =>
      rw [EncodingMachines.loopState_succ]
      dsimp only [upd]
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
      rw [ih]
      have hdec : BinArith.decWords (Strategy.encodeMsgs
          (phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i)) =
          phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) i :=
        (congrArg BinArith.decWords (encodeMsgs_eq_encWords _)).trans
          (BinArith.decWords_encWords _)
      rw [hdec, phasePrefix_succ, CommitmentLemmas.encodeMsgs_append,
        CommitmentLemmas.encodeMsgs_append]
  -- The phase-independent normalized-message bound supplies the loop's polynomial envelope.
  obtain ⟨C, c, hC⟩ := hX.output_length_le
  let XP : PolyExpr := .normal C c
  let bound : PolyExpr := .mul (.mul (Q.subst XP) (k.subst XP))
    (.add (.mul (.const 2) (B.subst XP)) (.const 2))
  have hN := EncodingMachines.unaryPolyOf_poly Q (EncodingMachines.unaryLength_poly hX)
  have hloop := ColMachines.polyTimeComputable_loopState' hupd (polyTimeComputable_const [])
    hN bound (fun w i hi => by
      rw [hclosed]
      have hx : (X w).length ≤ XP.eval w.length := by
        simpa only [XP, PolyExpr.eval_normal] using hC w
      have hq := Q.eval_mono hx
      have hk := k.eval_mono hx
      have hb := B.eval_mono hx
      simp only [bound, PolyExpr.eval_mul, PolyExpr.eval_add, PolyExpr.eval_const,
        PolyExpr.eval_subst]
      calc
        _ ≤ i * k.eval (X w).length * (2 * B.eval (X w).length + 2) :=
          length_encodeMsgs_phasePrefix_le S k B verifierFirst (X w) (Z w) (RV w) (RS w) i
        _ ≤ Q.eval (X w).length * k.eval (X w).length *
            (2 * B.eval (X w).length + 2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hi)
        _ ≤ Q.eval (XP.eval w.length) * k.eval (XP.eval w.length) *
            (2 * B.eval (XP.eval w.length) + 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul hq hk) (by omega))
  exact hloop.congr fun w => hclosed w _

/-- For uniform phase simulator `S`, polynomials `k,B,Q,CV`, and orientation `verifierFirst`,
there is a uniform simulator `SQ` with coin polynomial `CV + Q*S.coins`. On `(x,z)` it samples
one verifier tape from the first `CV(|x|)` coins, uses the remaining coins for the `Q(|x|)`
phase calls, and outputs the canonical view with their normalized prefix.
[PS10, Theorem 175.1; Gol01, §4.3.4, strict-PPT sequential simulation].
`∃ SQ : NUPPT, SQ.Uniform ∧ SQ.coins = .add CV (.mul Q S.coins) ∧ ∀ x z (r : SQ.Coins x.length),
SQ.simulate x z r = let rV := (List.ofFn r).take (CV.eval x.length); let rS := (List.ofFn r).drop
(CV.eval x.length); View.encode ⟨x, z, rV, phasePrefix S k B verifierFirst x z rV rS (Q.eval
x.length)⟩`.

**Proof sketch.** Apply `phasePrefix_poly` to the common-input and auxiliary-input projections
of the simulator layout, the first verifier-tape coin slice and the remaining phase tape.
Pair these fields with the encoded prefix to produce the canonical view. The published
`NUPPT.ofPolyTimeUniform` construction uses exactly the stated coin polynomial. Its activation
and simulator readers, followed by the layout projection equations, give the exact formula.
This includes empty prefixes when the phase count or round count is zero. -/
theorem exists_phaseSimulator (S : NUPPT) (hS : S.Uniform) (k B Q CV : PolyExpr)
    (verifierFirst : Bool) :
    ∃ SQ : NUPPT, SQ.Uniform ∧ SQ.coins = .add CV (.mul Q S.coins) ∧
      ∀ x z (r : SQ.Coins x.length), SQ.simulate x z r =
        let rV := (List.ofFn r).take (CV.eval x.length)
        let rS := (List.ofFn r).drop (CV.eval x.length)
        View.encode ⟨x, z, rV, phasePrefix S k B verifierFirst x z rV rS (Q.eval x.length)⟩ := by
  -- Decode both inputs and split the verifier and phase tapes through public PT readers.
  let X : List Bool → List Bool := fun w => pairFstD (NUPPT.inArg w)
  let Z : List Bool → List Bool := fun w => pairSndD (NUPPT.inArg w)
  let RV : List Bool → List Bool := fun w => (NUPPT.inCoins w).take (CV.eval (X w).length)
  let RS : List Bool → List Bool := fun w => (NUPPT.inCoins w).drop (CV.eval (X w).length)
  have hX : PolyTimeComputable X :=
    polyTimeComputable_pairFstD.comp NUPPT.polyTimeComputable_inArg
  have hZ : PolyTimeComputable Z :=
    polyTimeComputable_pairSndD.comp NUPPT.polyTimeComputable_inArg
  have hcut := hX.pairEncode NUPPT.polyTimeComputable_inCoins
  have hRV : PolyTimeComputable RV := by
    refine ((polyTimeComputable_pairTakePoly CV).comp hcut).congr fun w => ?_
    rw [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hRS : PolyTimeComputable RS := by
    refine ((polyTimeComputable_pairDropPoly CV).comp hcut).congr fun w => ?_
    rw [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  -- Assemble the normalized repeated prefix and encode the complete canonical view.
  have hpre := phasePrefix_poly S hS k B Q verifierFirst hX hZ hRV hRS
  let F : List Bool → List Bool := fun w =>
    View.encode ⟨X w, Z w, RV w,
      phasePrefix S k B verifierFirst (X w) (Z w) (RV w) (RS w) (Q.eval (X w).length)⟩
  have hF : PolyTimeComputable F := by
    refine ((hX.pairEncode hZ).pairEncode (hRV.pairEncode hpre)).congr fun w => ?_
    dsimp only [F]
    rw [View.encode_mk]
  -- The uniform constructor and activation/layout readers identify every output field.
  refine ⟨NUPPT.ofPolyTimeUniform hF (.add CV (.mul Q S.coins)),
    NUPPT.ofPolyTimeUniform_uniform hF _, NUPPT.coins_ofPolyTimeUniform hF _, ?_⟩
  intro x z r
  rw [NUPPT.simulate_eq, NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform,
    NUPPT.advInput_eq, ← NUPPT.layout_eq]
  dsimp only [F, X, Z, RV, RS]
  rw [NUPPT.inArg_layout, NUPPT.inCoins_layout, pairFstD_pairEncode, pairSndD_pairEncode]

end TCSlib.Cryptography.SequentialZK
