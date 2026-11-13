/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Asymptotic.Adversary
import TCSlib.Cryptography.Games.Probability
import TCSlib.Complexity.ClassNP.PolyTimeBlockLoop
import Mathlib.Data.List.GetD

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Bit-string oracles and their machine codec

The security games of [PS10] ch. 5–8 give machine adversaries a finite family of oracles on
fixed-length bit strings: a tagging oracle, a signing oracle, encryption and decryption oracles,
and so on. At parameter `n` oracle `i` takes `din i` bits and answers with `dout i` bits
(`bitSpec`). This file fixes the codec through which a next-move machine (`NUPPT.toComp`) plays
against such a family, and through which it returns a fixed-length output (`bitCodec`):
- **a query** to oracle `i` on `x` is the output `⟨[false], ⟨1^i, x⟩⟩`;
- **a final output** `a` is `⟨[true], a⟩`;
- **anything else**, a malformed or wrong-length string, decodes to the all-`false` output (the
  ch. 2–4 layer's convention D7: ill-formed outputs count as a fixed default);
- **a log entry** `(i, x, y)` is encoded as `⟨1^i, ⟨x, y⟩⟩`;
- **when the query budget runs out**, the output is the all-`false` string.

It is the shared codec of every prong's statements, and the T0 definitions of the efficiency fill
(`briefs/pass-shelat-ch5-8/fills/efficiency/`).

## Main definitions

* `Games.bitSpec din dout`: `k` oracles on fixed-length bit strings.
* `Games.decodeIdx`, `Games.decodeBitMove`: decoding of an oracle index and of a machine output as
  a move.
* `Games.encodeBitMove`: the canonical word of a move.
* `Games.bitCodec din dout dα`: the codec.
* `Games.castImpl`: an implementation of bit-string oracles read along equal length functions.
* `Games.cntRead`, `Games.ansRead`: the per-entry readings of an encoded log (one token for a
  nonempty log; the answer of the first entry).

## Main results

* `Games.decodeIdx_replicate`, `Games.decodeBitMove_query`, `Games.decodeBitMove_ret`: the
  well-formed encodings decode as intended.
* `Games.decodeIdx_eq_some_iff`, `Games.decodeBitMove_eq_query_iff`: only the canonical words
  decode as an index or a query.
* `Games.decodeBitMove_of_not_canonical`: every other word decodes to the all-`false` output.
* `Games.padFin_ofFn_zeroBits`, `Games.padFin_replicate_false`, `Games.padFin_nil`,
  `Games.decodeFin_nil_getD`: all-`false` strings and the empty answer read as `zeroBits`.
* `Games.padFin_append_split`: the two parts of a padded concatenation.
* `Games.simulate_castImpl_toCompOn`, `Games.expect_simulate_castImpl_toCompOn`: transport of a
  machine's run between two codecs with equal lengths.
* `Games.polyTimeComputable_cntRead`, `Games.polyTimeComputable_ansRead`: the per-entry readings
  are polynomial-time.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §3.8.1 (oracle machines) and Definitions 134.2, 136.2 and 168.1 (oracle adversaries).
-/

namespace TCSlib.Cryptography.Games

open Complexity Turing

/-! Seal B (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/Games/BitCodec.lean`, with every seal candidate of its
full TCSlib import closure (285 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.TimeConstructible _root_.Complexity.blockDone _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.xorD _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


variable {k : ℕ}

/-- **`k` oracles on fixed-length bit strings:** oracle `i` takes `din i` bits and answers with
`dout i` bits. -/
abbrev bitSpec (din dout : Fin k → ℕ) : OracleSpec (Fin k) :=
  ⟨fun i => Fin (din i) → Bool, fun i => Fin (dout i) → Bool⟩

/-- Oracle `i` of `bitSpec din dout` takes `din i`-bit strings. -/
theorem bitSpec_dom (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).dom i = (Fin (din i) → Bool) :=
  rfl

/-- Oracle `i` of `bitSpec din dout` answers with `dout i`-bit strings. -/
theorem bitSpec_rng (din dout : Fin k → ℕ) (i : Fin k) :
    (bitSpec din dout).rng i = (Fin (dout i) → Bool) :=
  rfl

/-- Decoding of an oracle index written in unary: `1^i` with `i < k` is `i`; every other word
(one containing `false`, or of length at least `k`) is `none`. -/
def decodeIdx (k : ℕ) (iw : List Bool) : Option (Fin k) :=
  if h : iw.length < k ∧ iw = List.replicate iw.length true then some ⟨iw.length, h.1⟩ else none

/-- The unary code of an index decodes to it. -/
theorem decodeIdx_replicate (i : Fin k) : decodeIdx k (List.replicate i true) = some i := by
  unfold decodeIdx
  have h : (List.replicate (i : ℕ) true).length < k ∧
      List.replicate (i : ℕ) true =
        List.replicate (List.replicate (i : ℕ) true).length true := by
    simp
  rw [dif_pos h]
  exact congrArg some (Fin.ext (by simp))

/-- **Exactly the unary codes decode**, each to its index:
`decodeIdx k iw = some i ↔ iw = 1^i`. -/
theorem decodeIdx_eq_some_iff {iw : List Bool} {i : Fin k} :
    decodeIdx k iw = some i ↔ iw = List.replicate i true := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeIdx_replicate i⟩
  unfold decodeIdx at h
  split_ifs at h with hw
  rw [Option.some.injEq] at h
  rw [← h]
  exact hw.2

/-- **Every other word is rejected:** `decodeIdx k iw = none` exactly when `iw` is the unary code
of no index below `k`. -/
theorem decodeIdx_eq_none_iff {iw : List Bool} :
    decodeIdx k iw = none ↔ ∀ i : Fin k, iw ≠ List.replicate i true := by
  constructor
  · intro h i hi
    rw [decodeIdx_eq_some_iff.2 hi] at h
    exact Option.some_ne_none i h
  · intro h
    cases hd : decodeIdx k iw with
    | none => rfl
    | some i => exact absurd (decodeIdx_eq_some_iff.1 hd) (h i)

/-- The default output: the all-`false` string. -/
def zeroBits (d : ℕ) : Fin d → Bool := fun _ => false

/-- Every bit of the default output is `false`: `zeroBits d j = false`. -/
theorem zeroBits_apply (d : ℕ) (j : Fin d) : zeroBits d j = false :=
  rfl

/-- The default output, written as a string, is `d` copies of `false`:
`List.ofFn (zeroBits d) = List.replicate d false`. -/
theorem ofFn_zeroBits (d : ℕ) : List.ofFn (zeroBits d) = List.replicate d false := by
  rw [show zeroBits d = fun _ => false from rfl, List.ofFn_const]

/-- The all-`false` answer, read at any width, is all-`false`:
`padFin d ⟦zeroBits m⟧ = zeroBits d`. -/
theorem padFin_ofFn_zeroBits (d m : ℕ) : padFin d (List.ofFn (zeroBits m)) = zeroBits d := by
  funext i
  rw [padFin_apply, ofFn_zeroBits, zeroBits_apply, List.getD_eq_getElem?_getD,
    List.getElem?_replicate]
  split <;> rfl

/-- An all-`false` list reads as the all-`false` vector at every width:
`padFin d (List.replicate m false) = zeroBits d`. -/
theorem padFin_replicate_false (d m : ℕ) : padFin d (List.replicate m false) = zeroBits d := by
  rw [← ofFn_zeroBits, padFin_ofFn_zeroBits]

/-- The empty list reads as the all-`false` vector: `padFin d [] = zeroBits d`. -/
theorem padFin_nil (d : ℕ) : padFin d [] = zeroBits d := padFin_replicate_false d 0

/-- **The two parts of a padded concatenation:** if `|u| = d₁`, the first `d₁` bits of
`padFin (d₁ + d₂) (u ++ v)` are `padFin d₁ u` and the rest `padFin d₂ v` (`padFin_apply`,
`List.getD_append`, `List.getD_append_right`). -/
theorem padFin_append_split {d₁ d₂ : ℕ} (u v : List Bool) (hu : u.length = d₁) :
    (fun j : Fin d₁ => padFin (d₁ + d₂) (u ++ v) (Fin.castAdd d₂ j)) = padFin d₁ u ∧
      (fun j : Fin d₂ => padFin (d₁ + d₂) (u ++ v) (Fin.natAdd d₁ j)) = padFin d₂ v := by
  refine ⟨funext fun j => ?_, funext fun j => ?_⟩
  · rw [padFin_apply, padFin_apply, Fin.coe_castAdd, List.getD_append _ _ _ _ (by omega)]
  · rw [padFin_apply, padFin_apply, Fin.coe_natAdd, List.getD_append_right _ _ _ _ (by omega)]
    congr 1
    omega

/-- An empty answer decodes to all-`false` at every length:
`(decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ`. -/
theorem decodeFin_nil_getD (ℓ : ℕ) : (decodeFin ℓ []).getD (zeroBits ℓ) = zeroBits ℓ := by
  rw [decodeFin_eq]
  split
  · next h =>
    subst h
    funext i
    exact absurd i.isLt (Nat.not_lt_zero _)
  · rfl

/-- Decoding of a machine output as a move against `bitSpec din dout` with `dα`-bit outputs:
`⟨[false], ⟨1^i, x⟩⟩` with `i < k` and `|x| = din i` is the query `x` to oracle `i`;
`⟨[true], a⟩` with `|a| = dα` is the output `a`; anything else is the output `zeroBits dα`. -/
def decodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    Move (bitSpec din dout) (Fin dα → Bool) :=
  match pairDecode w with
  | some ([false], rest) =>
    match pairDecode rest with
    | some (iw, xw) =>
      match decodeIdx k iw with
      | some i =>
        match decodeFin (din i) xw with
        | some x => .query i x
        | none => .ret (zeroBits dα)
      | none => .ret (zeroBits dα)
    | none => .ret (zeroBits dα)
  | some ([true], aw) =>
    match decodeFin dα aw with
    | some a => .ret a
    | none => .ret (zeroBits dα)
  | _ => .ret (zeroBits dα)

/-- **The canonical word of a move:** the query `x` to oracle `i` is `⟨[false], ⟨1^i, x⟩⟩`, and
the output `a` is `⟨[true], a⟩`. `decodeBitMove` inverts it (`decodeBitMove_encodeBitMove`). -/
def encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ) :
    Move (bitSpec din dout) (Fin dα → Bool) → List Bool
  | .query i x => pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))
  | .ret a => pairEncode [true] (List.ofFn a)

/-- The canonical word of a query:
`encodeBitMove din dout dα (query i x) = ⟨[false], ⟨1^i, x⟩⟩`. -/
theorem encodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    encodeBitMove din dout dα (.query i x) =
      pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) :=
  rfl

/-- The canonical word of an output: `encodeBitMove din dout dα (ret a) = ⟨[true], a⟩`. -/
theorem encodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    encodeBitMove din dout dα (.ret a) = pairEncode [true] (List.ofFn a) :=
  rfl

/-- **The codec of bit-string oracles:** moves decoded by `decodeBitMove`, a log entry
`(i, x, y)` encoded as `⟨1^i, ⟨x, y⟩⟩`, and the all-`false` output when the budget runs out. -/
def bitCodec (din dout : Fin k → ℕ) (dα : ℕ) :
    MachineCodec (bitSpec din dout) (Fin dα → Bool) where
  decodeMove := decodeBitMove din dout dα
  encodeEntry e :=
    pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2))
  timeout := zeroBits dα

/-- The codec decodes moves with `decodeBitMove`: `(bitCodec din dout dα).decodeMove w =
decodeBitMove din dout dα w`. -/
theorem bitCodec_decodeMove (din dout : Fin k → ℕ) (dα : ℕ) (w : List Bool) :
    (bitCodec din dout dα).decodeMove w = decodeBitMove din dout dα w :=
  rfl

/-- The codec encodes the log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem bitCodec_encodeEntry (din dout : Fin k → ℕ) (dα : ℕ)
    (e : Σ i, (bitSpec din dout).dom i × (bitSpec din dout).rng i) :
    (bitCodec din dout dα).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  rfl

/-- When the budget runs out, the codec's output is all-`false`:
`(bitCodec din dout dα).timeout = zeroBits dα`. -/
theorem bitCodec_timeout (din dout : Fin k → ℕ) (dα : ℕ) :
    (bitCodec din dout dα).timeout = zeroBits dα :=
  rfl

/-- The codec's log encoding does not depend on the output length: `bitCodec din dout dα` and
`bitCodec din dout dα'` encode every log alike. -/
theorem encodeLog_bitCodec (din dout : Fin k → ℕ) (dα dα' : ℕ) (h : QueryLog (bitSpec din dout)) :
    (bitCodec din dout dα).encodeLog h = (bitCodec din dout dα').encodeLog h := by
  induction h with
  | nil => rw [MachineCodec.encodeLog_nil, MachineCodec.encodeLog_nil]
  | cons e h ih =>
    rw [MachineCodec.encodeLog_cons, MachineCodec.encodeLog_cons, ih, bitCodec_encodeEntry,
      bitCodec_encodeEntry]

/-- A well-formed query decodes as the query. -/
theorem decodeBitMove_query (din dout : Fin k → ℕ) (dα : ℕ) (i : Fin k)
    (x : Fin (din i) → Bool) :
    decodeBitMove din dout dα
        (pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x))) = .query i x := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeIdx_replicate, decodeFin_ofFn]

/-- A well-formed output decodes as the output. -/
theorem decodeBitMove_ret (din dout : Fin k → ℕ) (dα : ℕ) (a : Fin dα → Bool) :
    decodeBitMove din dout dα (pairEncode [true] (List.ofFn a)) = .ret a := by
  simp [decodeBitMove, pairDecode_pairEncode, decodeFin_ofFn]

/-- **Only the canonical query word decodes as a query:** `decodeBitMove din dout dα w` is the
query `x` to oracle `i` exactly when `w = ⟨[false], ⟨1^i, x⟩⟩` (the converse of
`decodeBitMove_query`).

**Proof sketch.** Follow `decodeBitMove`'s branches: only the branch in which the tag is `[false]`,
the rest parses as a pair, the index word decodes and the payload has the right length returns a
query. There, each successful parse determines its input: a parsed pair is the pairing of its parts
(`eq_pairEncode_of_pairDecode`), a decoded index word is `1^i` (`decodeIdx_eq_some_iff`), and a
decoded payload is `List.ofFn x`. -/
theorem decodeBitMove_eq_query_iff {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool} {i : Fin k}
    {x : Fin (din i) → Bool} :
    decodeBitMove din dout dα w = .query i x ↔
      w = pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)) := by
  refine ⟨fun h => ?_, fun h => h ▸ decodeBitMove_query din dout dα i x⟩
  unfold decodeBitMove at h
  split at h
  · rename_i rest hw
    split at h
    · rename_i iw xw hr
      split at h
      · rename_i j hj
        split at h
        · rename_i x' hx
          cases h
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr,
            decodeIdx_eq_some_iff.1 hj, (decodeFin_eq_some_iff _ _ _).1 hx]
        · cases h
      · cases h
    · cases h
  · split at h <;> cases h
  · cases h

/-- **The default:** a word that is neither a canonical query `⟨[false], ⟨1^i, x⟩⟩` nor a
canonical output `⟨[true], a⟩` decodes to the output `zeroBits dα`. With `decodeBitMove_query`
and `decodeBitMove_ret` this determines `decodeBitMove` on every word.

**Proof sketch.** Follow `decodeBitMove`'s branches. Every branch but two returns `zeroBits dα`.
In the query branch, the successful parses make `w` a canonical query word, as in
`decodeBitMove_eq_query_iff`, against `hq`; in the output branch, they make `w` a canonical output
word, against `hr`. -/
theorem decodeBitMove_of_not_canonical {din dout : Fin k → ℕ} {dα : ℕ} {w : List Bool}
    (hq : ∀ (i : Fin k) (x : Fin (din i) → Bool),
      w ≠ pairEncode [false] (pairEncode (List.replicate i true) (List.ofFn x)))
    (hr : ∀ a : Fin dα → Bool, w ≠ pairEncode [true] (List.ofFn a)) :
    decodeBitMove din dout dα w = .ret (zeroBits dα) := by
  unfold decodeBitMove
  split
  · rename_i rest hw
    split
    · rename_i iw xw hr'
      split
      · rename_i j hj
        split
        · rename_i x hx
          refine absurd ?_ (hq j x)
          rw [eq_pairEncode_of_pairDecode _ _ _ hw, eq_pairEncode_of_pairDecode _ _ _ hr',
            decodeIdx_eq_some_iff.1 hj, (decodeFin_eq_some_iff _ _ _).1 hx]
        · rfl
      · rfl
    · rfl
  · rename_i aw hw
    split
    · rename_i a ha
      refine absurd ?_ (hr a)
      rw [eq_pairEncode_of_pairDecode _ _ _ hw, (decodeFin_eq_some_iff _ _ _).1 ha]
    · rfl
  · rfl

/-- **Canonical words decode to their move:** `decodeBitMove (encodeBitMove m) = m`. -/
theorem decodeBitMove_encodeBitMove (din dout : Fin k → ℕ) (dα : ℕ)
    (m : Move (bitSpec din dout) (Fin dα → Bool)) :
    decodeBitMove din dout dα (encodeBitMove din dout dα m) = m := by
  cases m with
  | query i x => exact decodeBitMove_query din dout dα i x
  | ret a => exact decodeBitMove_ret din dout dα a

/-- Distinct moves have distinct canonical words. -/
theorem encodeBitMove_injective (din dout : Fin k → ℕ) (dα : ℕ) :
    Function.Injective (encodeBitMove din dout dα) := fun m m' h => by
  rw [← decodeBitMove_encodeBitMove din dout dα m, h, decodeBitMove_encodeBitMove]

/-! ### Readings of a log entry -/

/-- One token for a nonempty log and nothing for the empty one:
`cntRead v = if v = [] then [] else [true]`. Applied to the successive suffixes of an encoded log,
it counts the entries. -/
def cntRead (v : List Bool) : List Bool := if decide (v = []) then [] else [true]

/-- `cntRead v = if v = [] then [] else [true]`. -/
theorem cntRead_eq (v : List Bool) : cntRead v = if decide (v = []) then [] else [true] := rfl

/-- The token reading is polynomial-time: `PolyTimeComputable cntRead`. -/
theorem polyTimeComputable_cntRead : PolyTimeComputable cntRead :=
  polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [])
    (polyTimeComputable_const [true])

/-- The answer `y` of the first entry `⟨1^i, ⟨x, y⟩⟩` of an encoded log:
`ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
def ansRead (v : List Bool) : List Bool := pairSndD (pairSndD (pairFstD v))

/-- `ansRead v = pairSndD (pairSndD (pairFstD v))`. -/
theorem ansRead_eq (v : List Bool) : ansRead v = pairSndD (pairSndD (pairFstD v)) := rfl

/-- The answer reading is polynomial-time: `PolyTimeComputable ansRead`. -/
theorem polyTimeComputable_ansRead : PolyTimeComputable ansRead :=
  polyTimeComputable_pairSndD.comp (polyTimeComputable_pairSndD.comp polyTimeComputable_pairFstD)

/-! ### Transport along equal lengths -/

section Transport

open ProbComp

variable {σ : Type}

/-- **An implementation read along length functions:** answer the query `x` to oracle `i` of
`bitSpec ins outs` by asking `O` the query `padFin (ins' i) ⟦x⟧` and reading its answer `y` as
`padFin (outs i) ⟦y⟧`. When `ins = ins'` and `outs = outs'` this is `O` itself
(`castImpl_self`). -/
def castImpl {ins ins' outs outs' : Fin k → ℕ} (O : QueryImpl (bitSpec ins' outs') σ unifSpec) :
    QueryImpl (bitSpec ins outs) σ unifSpec :=
  fun i x s => (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
    .pure (padFin (outs i) (List.ofFn p.1), p.2)

/-- The defining equation of `castImpl`: `castImpl O i x s =
(O i (padFin (ins' i) ⟦x⟧) s).bind fun p => pure (padFin (outs i) ⟦p.1⟧, p.2)`. -/
theorem castImpl_eq {ins ins' outs outs' : Fin k → ℕ}
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool)
    (s : σ) :
    castImpl (ins := ins) (outs := outs) O i x s =
      (O i (padFin (ins' i) (List.ofFn x)) s).bind fun p =>
        .pure (padFin (outs i) (List.ofFn p.1), p.2) :=
  rfl

/-- Read along the same lengths, an implementation is unchanged: `castImpl O = O`. -/
theorem castImpl_self {ins outs : Fin k → ℕ} (O : QueryImpl (bitSpec ins outs) σ unifSpec) :
    castImpl (ins := ins) (outs := outs) O = O := by
  funext i x s
  rw [castImpl_eq, padFin_ofFn]
  simp only [padFin_ofFn]
  exact OracleComp.bind_pure _

/-- **Transport of a machine's run:** if `ins = ins'`, `outs = outs'` and `d = d'`, simulating
`castImpl O` on the run of `M` through `bitCodec ins outs d` gives, with outputs read as lists,
the simulation of `O` on the run of `M` through `bitCodec ins' outs' d'`.

**Proof sketch.** Substitute the equalities; then `castImpl O = O` (`castImpl_self`). -/
theorem simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) :
    (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) =
      (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s).bind
        (fun p => .pure (List.ofFn p.1, p.2)) := by
  subst hi ho hd
  rw [castImpl_self]

/-- **Transport of a machine's run, in expectation:** for every function `G` of the output (read
as a list) and the final state, `simulate_castImpl_toCompOn` in the form
`𝔼[G (⟦p.1⟧, p.2)]` over the two simulations. -/
theorem expect_simulate_castImpl_toCompOn {ins ins' outs outs' : Fin k → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d')
    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (M : NUPPT) (n q : ℕ) (x : List Bool)
    (r : M.Coins n) (s : σ) (G : List Bool × σ → ℝ) :
    expect (simulate (castImpl (ins := ins) (outs := outs) O)
        (M.toCompOn (bitCodec ins outs d) n q x r) s) (fun p => G (List.ofFn p.1, p.2)) =
      expect (simulate O (M.toCompOn (bitCodec ins' outs' d') n q x r) s)
        (fun p => G (List.ofFn p.1, p.2)) := by
  have h := congrArg (fun c => expect c G) (simulate_castImpl_toCompOn hi ho hd O M n q x r s)
  simp only [expect_bind, expect_pure] at h
  exact h

end Transport

end TCSlib.Cryptography.Games
