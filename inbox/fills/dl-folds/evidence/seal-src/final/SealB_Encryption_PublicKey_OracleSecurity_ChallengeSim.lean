/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Games.BitCodec
import TCSlib.Cryptography.Games.Machines
import TCSlib.Cryptography.Games.Probability
import TCSlib.Cryptography.Games.Hopping
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A deterministic challenge oracle under CPA

Under a chosen-plaintext attack the IND experiment of [PS10, Definition 171.5] has two oracles
in the encoding of `Encryption.PublicKey.OracleSecurity`: a decryption oracle that always
answers all-`false`, and a challenge oracle that answers the first query `⟨m₀, m₁⟩` with a
ciphertext and repeats it afterwards. This file studies that pair of oracles on bit strings of
arbitrary lengths (`bitSpec ins outs`) when the first challenge answer is a deterministic
function `g` of the query, for example once the encryption coins have been sampled in advance.

The run is a pure function of the computation (`chRun`). Its result depends on `g` only through
`g` at the first challenge query (`firstQ`), which does not depend on `g` at all
(`chRun_congr`). This replaces the informal "condition on the adversary's choice of messages"
in the proof of the claim after Definition 171.5. Both the run and the first query transport
along equalities of the length functions (`chRun_toCompOn_transport`), which aligns two codecs
with propositionally equal lengths.

The last section collects sampling identities used to rearrange the expectations of the CPA
reduction: reindexing by an equivalence, products, exchange of order, and singleton types.

## Main definitions

* `Composability.ChallengeSim.chRun g c s`: the run of `c` against the CPA oracles with the
  deterministic challenge answer `g`, from the challenge state `s`.
* `Composability.ChallengeSim.firstQ c`: the first challenge query of `c`, as a list.

## Main results

* `ChallengeSim.chRun_some_congr`: once the challenge is recorded, `g` no longer matters.
* `ChallengeSim.chRun_congr`: the run depends on `g` only at the first challenge query.
* `ChallengeSim.length_of_firstQ_eq_some`: the first challenge query has `ins 1` bits.
* `ChallengeSim.chRun_toCompOn_transport_list`, `ChallengeSim.chRun_toCompOn_transport`: transport
  along equal length functions, with a query-dependent and with a constant answer.
* `ChallengeSim.expect_simulate_eager`: eager challenge coins, for any CPA-shaped oracle.
* `ChallengeSim.expect_sample_prod`: sampling a product is sampling its factors (the other
  sampling identities are `Games.ProbComp`'s).
* `ChallengeSim.expect_indicator_sub`: the case split on the first challenge `(m₀, m₁)`.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability.ChallengeSim

open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games ProbComp

/-! Seal B (dl-folds, final): a verbatim copy of `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity/ChallengeSim.lean`, with every seal candidate of its
full TCSlib import closure (304 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.TimeConstructible _root_.Complexity.blockDone _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.xorD _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.ansRead _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.cntRead _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlock_flatten.match_1_1 _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.xorPerm _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


variable {ins outs : Fin 2 → ℕ} {α : Type}

/-! ### The deterministic run -/

/-- **The run of `c` against the CPA oracles with the challenge answer `g`**, from the challenge
state `s`: oracle `0` answers all-`false` and keeps the state; oracle `1` answers the first query
`mm` with `padFin (outs 1) (g mm)` and records it, and later repeats the recorded answer. The
result is `c`'s output and the final state. -/
def chRun (g : (Fin (ins 1) → Bool) → List Bool) :
    OracleComp (bitSpec ins outs) α → Option (Fin (outs 1) → Bool) →
      α × Option (Fin (outs 1) → Bool)
  | .pure a, s => (a, s)
  | .query 0 _ k, s => chRun g (k (zeroBits _)) s
  | .query 1 mm k, none => chRun g (k (padFin _ (g mm))) (some (padFin _ (g mm)))
  | .query 1 _ k, some c => chRun g (k c) (some c)

/-- A return ends the run: `chRun g (pure a) s = (a, s)`. -/
theorem chRun_pure (g : (Fin (ins 1) → Bool) → List Bool) (a : α)
    (s : Option (Fin (outs 1) → Bool)) : chRun g (.pure a) s = (a, s) := rfl

/-- A query to oracle `0` is answered all-`false`, keeping the state:
`chRun g (query 0 x k) s = chRun g (k 0) s`. -/
theorem chRun_query_zero (g : (Fin (ins 1) → Bool) → List Bool) (x : Fin (ins 0) → Bool)
    (k : (Fin (outs 0) → Bool) → OracleComp (bitSpec ins outs) α)
    (s : Option (Fin (outs 1) → Bool)) :
    chRun g (.query 0 x k) s = chRun g (k (zeroBits _)) s := rfl

/-- The first challenge query `mm` is answered with `padFin (outs 1) (g mm)`, which is recorded. -/
theorem chRun_query_one_none (g : (Fin (ins 1) → Bool) → List Bool) (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) :
    chRun g (.query 1 mm k) none = chRun g (k (padFin _ (g mm))) (some (padFin _ (g mm))) := rfl

/-- A later challenge query repeats the recorded answer `c`. -/
theorem chRun_query_one_some (g : (Fin (ins 1) → Bool) → List Bool) (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) (c : Fin (outs 1) → Bool) :
    chRun g (.query 1 mm k) (some c) = chRun g (k c) (some c) := rfl

/-- **The first challenge query** of `c` against the CPA oracles, as a list: queries to oracle `0`
are answered all-`false` and skipped; the first query `mm` to oracle `1` gives `List.ofFn mm`; a
computation that returns before it gives `none`. -/
def firstQ : OracleComp (bitSpec ins outs) α → Option (List Bool)
  | .pure _ => none
  | .query 0 _ k => firstQ (k (zeroBits _))
  | .query 1 mm _ => some (List.ofFn mm)

/-- A return asks no challenge: `firstQ (pure a) = none`. -/
theorem firstQ_pure (a : α) : firstQ (ins := ins) (outs := outs) (.pure a) = none := rfl

/-- A query to oracle `0` is skipped: `firstQ (query 0 x k) = firstQ (k 0)`. -/
theorem firstQ_query_zero (x : Fin (ins 0) → Bool)
    (k : (Fin (outs 0) → Bool) → OracleComp (bitSpec ins outs) α) :
    firstQ (.query 0 x k) = firstQ (k (zeroBits _)) := rfl

/-- A query `mm` to oracle `1` is the first challenge: `firstQ (query 1 mm k) = some ⟦mm⟧`. -/
theorem firstQ_query_one (mm : Fin (ins 1) → Bool)
    (k : (Fin (outs 1) → Bool) → OracleComp (bitSpec ins outs) α) :
    firstQ (.query 1 mm k) = some (List.ofFn mm) := rfl

/-- **Once the challenge is recorded, the answer function no longer matters**:
`chRun g c (some C) = chRun g' c (some C)`.

**Proof sketch.** Induction on `c`: from a recorded state both runs answer oracle `0` with
all-`false` and oracle `1` with the recorded `C`, and keep the state. -/
theorem chRun_some_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
    (c : OracleComp (bitSpec ins outs) α) (C : Fin (outs 1) → Bool) :
    chRun g c (some C) = chRun g' c (some C) := by
  induction c with
  | pure a => rfl
  | query i x k ih =>
    match i, x, k, ih with
    | 0, x, k, ih => rw [chRun_query_zero, chRun_query_zero, ih]
    | 1, x, k, ih => rw [chRun_query_one_some, chRun_query_one_some, ih]

/-- **Eager challenge coins, for any CPA-shaped oracle.** Let `impl` answer oracle `0`
all-`false`, a challenge from a recorded state `c` with `c`, and the first challenge `mm` by
sampling `re` and answering (and recording) `padFin d (g mm re)`; the state holds `d`-bit
strings, `d = outs 1`, read through the cast `e`. Then for every `G`,
`𝔼[G ∘ fst] (simulate impl c s) = 𝔼_{re} G (chRun (fun mm => g mm re) c (s.map (cast e))).1`.

**Proof sketch.** Substitute `d = outs 1`, so that the casts are identities. With the coins `re`
fixed, `impl` becomes the deterministic oracle `OE re`, whose simulation is the run
`chRun (fun mm => g mm re)` (induction on the computation). From the unchallenged state,
`Games.expect_simulate_eager` (the coins are spent at the first challenge, after which the state
is recorded) averages `OE re` over `re`. From a recorded state `impl` is already deterministic,
so its simulation is the run for any `re`, which does not depend on `re` (`chRun_some_congr`). -/
theorem expect_simulate_eager {ins outs : Fin 2 → ℕ} {d : ℕ} (hd : outs 1 = d)
    (e : (Fin d → Bool) = (Fin (outs 1) → Bool)) {R : Type} [Fintype R] [Nonempty R]
    (impl : QueryImpl (bitSpec ins outs) (Option (Fin d → Bool)) unifSpec)
    (g : (Fin (ins 1) → Bool) → R → List Bool)
    (h0 : ∀ x s, impl 0 x s = .pure (zeroBits _, s))
    (hrep : ∀ mm c, impl 1 mm (some c) = .pure (cast e c, some c))
    (hnew : ∀ mm, impl 1 mm none = (ProbComp.sample R).bind fun re =>
      .pure (cast e (padFin d (g mm re)), some (padFin d (g mm re))))
    {α : Type} (G : α → ℝ) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin d → Bool)) :
    expect (simulate impl c s) (fun p => G p.1) =
      expect (ProbComp.sample R) fun re =>
        G (chRun (fun mm => g mm re) c (s.map (cast e))).1 := by
  subst hd
  have hc : ∀ x : Fin (outs 1) → Bool, cast e x = x := fun x => cast_eq e x
  have hmap : ∀ s : Option (Fin (outs 1) → Bool), s.map (cast e) = s := fun s => by
    cases s <;> simp
  simp only [hc] at hrep hnew
  simp only [hmap]
  -- The oracle with the coins `re` fixed in advance.
  let OE : R → QueryImpl (bitSpec ins outs) (Option (Fin (outs 1) → Bool)) unifSpec :=
    fun re i x s => match i, x, s with
      | 0, _, s => .pure (zeroBits _, s)
      | 1, mm, none => .pure (padFin _ (g mm re), some (padFin _ (g mm re)))
      | 1, _, some c => .pure (c, some c)
  -- Its simulation is the run with the answer `g · re`.
  have hdet : ∀ (re : R) (c : OracleComp (bitSpec ins outs) α) (s : Option (Fin (outs 1) → Bool)),
      simulate (OE re) c s = .pure (chRun (fun mm => g mm re) c s) := by
    intro re c
    induction c with
    | pure a => exact fun s => by rw [simulate_pure, chRun_pure]
    | query i x k ih =>
      intro s
      match i, x, k, ih, s with
      | 0, x, k, ih, s =>
        rw [simulate_query, chRun_query_zero]
        show (OracleComp.pure (zeroBits _, s)).bind (fun p => simulate (OE re) (k p.1) p.2) = _
        rw [OracleComp.pure_bind]
        exact ih _ s
      | 1, x, k, ih, none =>
        rw [simulate_query, chRun_query_one_none]
        show (OracleComp.pure (padFin _ (g x re), some (padFin _ (g x re)))).bind
          (fun p => simulate (OE re) (k p.1) p.2) = _
        rw [OracleComp.pure_bind]
        exact ih _ _
      | 1, x, k, ih, some C =>
        rw [simulate_query, chRun_query_one_some]
        show (OracleComp.pure (C, some C)).bind (fun p => simulate (OE re) (k p.1) p.2) = _
        rw [OracleComp.pure_bind]
        exact ih _ _
  -- From a recorded state, `impl` is the oracle with any coins fixed.
  have hsome : ∀ (re : R) (c : OracleComp (bitSpec ins outs) α) (C : Fin (outs 1) → Bool),
      simulate impl c (some C) = simulate (OE re) c (some C) := by
    intro re c
    induction c with
    | pure a => exact fun C => by rw [simulate_pure, simulate_pure]
    | query i x k ih =>
      intro C
      match i, x, k, ih with
      | 0, x, k, ih =>
        rw [simulate_query, simulate_query, h0, OracleComp.pure_bind]
        show _ = (OracleComp.pure (zeroBits _, some C)).bind
          (fun p => simulate (OE re) (k p.1) p.2)
        rw [OracleComp.pure_bind]
        exact ih _ C
      | 1, x, k, ih =>
        rw [simulate_query, simulate_query, hrep, OracleComp.pure_bind]
        show _ = (OracleComp.pure (C, some C)).bind (fun p => simulate (OE re) (k p.1) p.2)
        rw [OracleComp.pure_bind]
        exact ih _ C
  cases s with
  | none =>
    rw [Games.expect_simulate_eager impl OE (fun s => s.isSome = true)
      (fun re i x s hs => ?_) (fun i x s hs => ?_) (fun i x s hs => ?_) c (fun p => G p.1)
      (by simp)]
    · refine congrArg _ (funext fun re => ?_)
      rw [hdet, expect_pure]
    · obtain ⟨C, rfl⟩ := Option.isSome_iff_exists.1 hs
      match i, x with
      | 0, x => exact (h0 x _).symm
      | 1, x => exact (hrep x C).symm
    · obtain ⟨C, rfl⟩ := Option.isSome_iff_exists.1 hs
      match i, x with
      | 0, x => rw [h0]; exact OracleComp.allOutputs_pure.2 rfl
      | 1, x => rw [hrep]; exact OracleComp.allOutputs_pure.2 rfl
    · obtain rfl : s = none := by simpa using hs
      match i, x with
      | 0, x =>
        exact .inl fun re => ⟨(h0 x none).symm, by
          rw [h0]
          exact OracleComp.allOutputs_pure.2 (by simp)⟩
      | 1, x => exact .inr ⟨hnew x, fun re => OracleComp.allOutputs_pure.2 rfl⟩
  | some C =>
    rw [hsome (Classical.arbitrary R), hdet, expect_pure]
    refine (Eq.trans ?_ (expect_const (ProbComp.sample R) _)).symm
    refine congrArg _ (funext fun re => ?_)
    rw [chRun_some_congr (fun mm => g mm re) (fun mm => g mm (Classical.arbitrary R))]

/-- **First-challenge congruence:** if `g` and `g'` agree at the first challenge query of `c`
(vacuous when there is none), the runs from the unchallenged state agree:
`chRun g c none = chRun g' c none`.

**Proof sketch.** Induction on `c`. Queries to oracle `0` are answered all-`false` by both runs
and do not change the first challenge query. At the first query `mm` to oracle `1` both runs
record `padFin (g mm) = padFin (g' mm)`, and from then on `chRun_some_congr` applies. -/
theorem chRun_congr (g g' : (Fin (ins 1) → Bool) → List Bool)
    (c : OracleComp (bitSpec ins outs) α)
    (h : ∀ mm : Fin (ins 1) → Bool, firstQ c = some (List.ofFn mm) → g mm = g' mm) :
    chRun g c none = chRun g' c none := by
  induction c with
  | pure a => rfl
  | query i x k ih =>
    match i, x, k, ih, h with
    | 0, x, k, ih, h =>
      rw [chRun_query_zero, chRun_query_zero]
      exact ih _ fun mm hmm => h mm (by rw [firstQ_query_zero]; exact hmm)
    | 1, x, k, ih, h =>
      have hx : g x = g' x := h x (firstQ_query_one x k)
      rw [chRun_query_one_none, chRun_query_one_none, hx]
      exact chRun_some_congr g g' _ _

/-- **The first challenge query has the challenge length**: if `firstQ c = some l` then
`|l| = ins 1`.

**Proof sketch.** Induction on `c`: the first query to oracle `1` is `List.ofFn mm` with
`mm : Fin (ins 1) → Bool`. -/
theorem length_of_firstQ_eq_some (c : OracleComp (bitSpec ins outs) α) {l : List Bool}
    (h : firstQ c = some l) : l.length = ins 1 := by
  induction c with
  | pure a => exact absurd h (by rw [firstQ_pure]; exact Option.noConfusion)
  | query i x k ih =>
    match i, x, k, ih, h with
    | 0, x, k, ih, h =>
      rw [firstQ_query_zero] at h
      exact ih _ h
    | 1, x, k, _, h =>
      rw [firstQ_query_one, Option.some.injEq] at h
      rw [← h, List.length_ofFn]

/-- **Transport of a run with a query-dependent answer along equal lengths:** for a machine
adversary run through `bitCodec`, if `ins = ins'`, `outs = outs'` and `d = d'`, then for every
`G : List Bool → List Bool`,
`List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun y => G ⟦y⟧) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1`, and
the two runs have the same `firstQ`.

**Proof sketch.** Substitute the equalities; both sides become identical. -/
theorem chRun_toCompOn_transport_list {ins' outs' : Fin 2 → ℕ} {d d' : ℕ}
    (hi : ins = ins') (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool)
    (r : A.Coins n) (G : List Bool → List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun y => G (List.ofFn y))
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) := by
  subst hi ho hd
  exact ⟨rfl, rfl⟩

/-- **Transport along equal lengths:** for a machine adversary run through `bitCodec`, if
`ins = ins'`, `outs = outs'` and `d = d'`, then
`List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
List.ofFn (chRun (fun _ => w) (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1` and the
two runs have the same `firstQ`.

**Proof sketch.** `chRun_toCompOn_transport_list` with the constant answer `G = fun _ => w`. -/
theorem chRun_toCompOn_transport {ins' outs' : Fin 2 → ℕ} {d d' : ℕ} (hi : ins = ins')
    (ho : outs = outs') (hd : d = d') (A : NUPPT) (n q : ℕ) (x : List Bool) (r : A.Coins n)
    (w : List Bool) :
    List.ofFn (chRun (ins := ins) (outs := outs) (fun _ => w)
        (A.toCompOn (bitCodec ins outs d) n q x r) none).1 =
      List.ofFn (chRun (ins := ins') (outs := outs') (fun _ => w)
        (A.toCompOn (bitCodec ins' outs' d') n q x r) none).1 ∧
    firstQ (A.toCompOn (bitCodec ins outs d) n q x r) =
      firstQ (A.toCompOn (bitCodec ins' outs' d') n q x r) :=
  chRun_toCompOn_transport_list hi ho hd A n q x r fun _ => w

/-! ### Sampling identities -/

section Sampling

variable {β : Type}

/-- **Sampling a product is sampling its factors:**
`𝔼_{(a, b) ← α × β} g (a, b) = 𝔼_{a ← α} 𝔼_{b ← β} g (a, b)`. -/
theorem expect_sample_prod [Fintype α] [Nonempty α] [Fintype β] [Nonempty β]
    (g : α × β → ℝ) :
    expect (sample (α × β)) g = expect (sample α) fun a => expect (sample β) fun b => g (a, b) := by
  rw [← Bridge.expect_sample_pair]
  simp only [expect_bind, expect_pure]

/-- **The pointwise case split of the CPA reduction:** for the first challenge `(m₀, m₁)`, the
difference of the acceptance rates of `A` against `Enc(m₀)` and `Enc(m₁)` equals the difference of
the acceptance rates of the post-processed bit `(m₀ ≠ m₁) ∧ (a ≠ m₀)` against `Enc(0)` and `Enc(1)`.

**Proof sketch.** Four cases. Equal messages give `0 = 0`; `(0, 1)` gives the same difference;
`(1, 0)` gives `(1 − p₀) − (1 − p₁) = p₁ − p₀` for the negated bit. -/
theorem expect_indicator_sub {ρ : Type} [Fintype ρ] [Nonempty ρ] (f : Bool → ρ → Bool)
    (m₀ m₁ : Bool) :
    expect (sample ρ) (fun re => if f m₀ re = true then (1 : ℝ) else 0) -
        expect (sample ρ) (fun re => if f m₁ re = true then (1 : ℝ) else 0) =
      expect (sample ρ)
          (fun re => if ((m₀ != m₁) && (f false re != m₀)) = true then (1 : ℝ) else 0) -
        expect (sample ρ)
          (fun re => if ((m₀ != m₁) && (f true re != m₀)) = true then (1 : ℝ) else 0) := by
  have hneg : ∀ x : Bool, (if (!x) = true then (1 : ℝ) else 0) = 1 - if x = true then 1 else 0 := by
    intro x
    cases x <;> norm_num
  have hf : ∀ x : Bool, (x != false) = x := fun x => by cases x <;> rfl
  have ht : ∀ x : Bool, (x != true) = !x := fun x => by cases x <;> rfl
  cases m₀ <;> cases m₁
  · simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, expect_const,
      sub_self]
  · simp only [show (false != true) = true from rfl, Bool.true_and, hf]
  · simp only [show (true != false) = true from rfl, Bool.true_and, ht, hneg, expect_sub,
      expect_const]
    ring
  · simp only [bne_self_eq_false, Bool.false_and, Bool.false_eq_true, if_false, expect_const,
      sub_self]

end Sampling

end TCSlib.Cryptography.Composability.ChallengeSim
