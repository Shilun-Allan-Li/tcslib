/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.FromPRG
import TCSlib.Cryptography.Encryption.PrivateKey.OracleSecurity
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Encryption.PublicKey.EnsembleSecurity
import TCSlib.Complexity.ClassP.BinaryArith.Loops
import TCSlib.Cryptography.Games.Bridges.Experiments

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# CPA, CCA1 and CCA2 security of public-key encryption

[PS10, Definition 171.5], the public-key form of Definition 168.1: `(pk, sk) ← Gen(1^n)`;
`(m₀, m₁, state) ← A^{O₁(sk)}(1^n, pk)`; `c ← Enc_pk(m_b)`; output `A^{O₂(sk)}(c, state)`. The
oracle pairs are `[·, ·]` (CPA), `[Dec, ·]` (CCA1) and `[Dec, Dec*]` (CCA2), where `Dec*` answers
every query except the challenge. There is no encryption oracle: the adversary holds `pk`.
The trapdoor application of Claim 172.a is in `Encryption.PublicKey.TrapdoorCPA`.

**Its encoding.** As in the private-key game (`Encryption/PrivateKey/OracleSecurity.lean`), one
machine plays both phases. It takes `pk` and queries the bit-string oracles `Dec` and `Challenge`.
The oracle state records the challenge and uses it to gate `Dec` by phase (`decOpen`).

**Fixed lengths by canonical padding** (ruling of 2026-11-05). The codec's oracles take and return
fixed-length strings. Public-key schemes of the ch. 2–4 layer have ciphertexts of varying length,
for example Algorithm 104.3's `⟨f_i(r), b ⊕ m⟩`. A generic wrapper (`FixedLengthPKScheme.ofPadded`)
pads every ciphertext `c` to `L(n)` bits as `⟨c, 1^{L(n) − 2|c| − 2}⟩` (`padCt`). Its decryptor
answers `⊥` on every string that is not such a canonical padding (`isPadded`). Without that check
the padded scheme would be malleable: changing a padding bit of the challenge gives a different
string that decrypts to the same message, which breaks CCA2. Padding is a bijection between
ciphertexts and canonical strings (`pairFstD_padCt`, `padCt_of_isPadded`). So `Dec*` refusing the
padded challenge is `Dec*` refusing the challenge. A bound `L` always exists
(`PublicKeyScheme.exists_padBound`, from the machines' time bounds).

**Deviations** (beyond those of Definition 168.1): ciphertexts reach the adversary padded, and
`Dec` takes only `L(n)`-bit queries, so it decrypts only ciphertexts with `2|c| + 2 ≤ L(n)`.
Security is stated for each admissible `L`; a larger `L` admits longer `Dec` queries.

## Main definitions

* `Composability.padCt`, `Composability.isPadded`: canonical padding and its test.
* `Composability.FixedLengthPKScheme`: a public-key scheme with `msgLen(n)`-bit messages and
  `ctLen(n)`-bit ciphertexts; `FixedLengthPKScheme.ofPadded` builds one by padding.
* `PublicKeyScheme.padded`, `BitPublicKeyScheme.padded`: the ch. 2–4 schemes, padded.
* `FixedLengthPKScheme.indImpl`, `indGame`, `INDSecure`: [PS10, Definition 171.5].

## Main results

* `pairFstD_padCt`, `isPadded_padCt`, `padCt_of_isPadded`: padding is a bijection onto the
  canonical strings.
* `PublicKeyScheme.exists_padBound`, `BitPublicKeyScheme.exists_padBound`: padding bounds exist.
* `FixedLengthPKScheme.indCodec_eq_bitCodec`: the adversary codec is a bit codec;
  `PublicKeyScheme.padded_enc_runAt`, `padded_enc_coins`: the padded encryptor.

The claim after Definition 171.5, `BitPublicKeyScheme.SingleBitSecure.padded_cpa` (single-bit
security gives CPA security), and its eager-coins lemma `expect_simulate_indImpl_cpa` are in
`OracleSecurity.PaddedCPA`. Its helpers are `OracleSecurity.ChallengeSim` (the deterministic CPA
run and first-challenge congruence) and `OracleSecurity.RecordHandler` (the recording handler
for T1).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.4, Definition 171.5 and the claim after it on Construction 104.3 (book pp. 171–172).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal B (dl-folds, base): a verbatim copy of `TCSlib/Cryptography/Encryption/PublicKey/OracleSecurity.lean`, with every seal candidate of its
full TCSlib import closure (709 definitions, `PolyExpr.eval` included) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Composability.Attack.ofNat _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.castImpl _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PrivateKeyScheme.Deterministic _root_.TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.encDist _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList.match_1 _root_.TCSlib.Cryptography.PrivateKeyScheme.firstTwoEqFun _root_.TCSlib.Cryptography.PrivateKeyScheme.multiEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PublicKeyScheme.Secure _root_.TCSlib.Cryptography.PublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blockEmit _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockList _root_.TCSlib.Cryptography.blockList.match_1 _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.blockStep _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decListEmit _root_.TCSlib.Cryptography.decListFun _root_.TCSlib.Cryptography.decListStep _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.hybridAdv _root_.TCSlib.Cryptography.hybridCoins _root_.TCSlib.Cryptography.hybridPlant _root_.TCSlib.Cryptography.hybridPre _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.length_flatten_ofFn.match_1_1 _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multiDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padXor _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgPadFun _root_.TCSlib.Cryptography.prgScheme _root_.TCSlib.Cryptography.prgScheme_encCoinsEquiv _root_.TCSlib.Cryptography.prgScheme_genCoinsEquiv _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.singleDist _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-! ### Canonical padding -/

/-- **Canonical padding** of a ciphertext `c` to `L` bits: `⟨c, 1^{L − 2|c| − 2}⟩`. -/
def padCt (L : ℕ) (c : List Bool) : List Bool :=
  pairEncode c (List.replicate (L - (2 * c.length + 2)) true)

/-- Padding pairs `c` with `L - (2 * c.length + 2)` true bits. -/
theorem padCt_eq (L : ℕ) (c : List Bool) :
    padCt L c = pairEncode c (List.replicate (L - (2 * c.length + 2)) true) := rfl

/-- Whether `w` is a canonical padding: a pair `⟨c, s⟩` whose second part `s` is all `true`. -/
def isPadded (w : List Bool) : Bool :=
  decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)

/-- The canonical-padding test checks that `w` is its decoded pair and that its second
component contains no false bit. -/
theorem isPadded_eq (w : List Bool) :
    isPadded w =
      (decide (pairEncode (pairFstD w) (pairSndD w) = w) && !BinArith.hasFalse (pairSndD w)) := rfl

/-- A padding to `L ≥ 2|c| + 2` bits has `L` bits. -/
theorem length_padCt {L : ℕ} {c : List Bool} (h : 2 * c.length + 2 ≤ L) :
    (padCt L c).length = L := by
  simp only [padCt, length_pairEncode, List.length_replicate]
  omega

/-- Unpadding recovers the ciphertext. -/
@[simp] theorem pairFstD_padCt (L : ℕ) (c : List Bool) : pairFstD (padCt L c) = c := by
  simp [padCt]

/-- A padding is canonical. -/
theorem isPadded_padCt (L : ℕ) (c : List Bool) : isPadded (padCt L c) = true := by
  simp [isPadded, padCt, BinArith.hasFalse_eq]

/-- A canonical string is the padding of its first part to its own length. -/
theorem padCt_of_isPadded {w : List Bool} (h : isPadded w = true) :
    padCt w.length (pairFstD w) = w := by
  simp only [isPadded, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  obtain ⟨h₁, h₂⟩ := h
  have hall : pairSndD w = List.replicate (pairSndD w).length true := by
    refine List.eq_replicate_iff.2 ⟨rfl, fun b hb => ?_⟩
    cases b
    · simp only [BinArith.hasFalse_eq, List.any_eq_false, List.mem_map, id_eq,
        forall_exists_index, and_imp] at h₂
      exact absurd rfl (h₂ _ false hb rfl)
    · rfl
  have hlen : w.length = 2 * (pairFstD w).length + 2 + (pairSndD w).length := by
    conv_lhs => rw [← h₁]
    simp only [length_pairEncode]
  unfold padCt
  rw [hlen, show 2 * (pairFstD w).length + 2 + (pairSndD w).length -
    (2 * (pairFstD w).length + 2) = (pairSndD w).length by omega, ← hall]
  exact h₁

/-- The canonical test is polynomial-time. -/
theorem polyTimeComputable_isPadded : PolyTimeComputable (fun w => [isPadded w]) := by
  have heq : PolyTimeComputable fun w => [decide (pairEncode (pairFstD w) (pairSndD w) = w)] := by
    convert polyTimeComputable_pairEq.comp
      ((polyTimeComputable_pairFstD.pairEncode polyTimeComputable_pairSndD).pairEncode
        polyTimeComputable_id) using 1
    funext w
    simp [Function.comp_apply]
  exact polyTimeComputable_and heq
    (polyTimeComputable_not (BinArith.polyTimeComputable_hasFalse.comp polyTimeComputable_pairSndD))

/-! ### The padded encryptor and decryptor -/

/-- The padded encryptor's string function: run `Enc` on the same parameter, argument and coins,
and pad its ciphertext to `L(n)` bits. -/
def padEncFun (enc : NUPPT) (L : PolyExpr) (z : List Bool) : List Bool :=
  padCt (L.eval (NUPPT.inParam z).length)
    (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)))

/-- The padded encryptor's string function pads the original output at the same parameter,
argument and coins, with empty advice, to the length prescribed by `L`. -/
theorem padEncFun_eq (enc : NUPPT) (L : PolyExpr) (z : List Bool) :
    padEncFun enc L z = padCt (L.eval (NUPPT.inParam z).length)
      (enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z))) := rfl

/-- The padded encryptor is polynomial-time. -/
theorem polyTimeComputable_padEncFun (enc : NUPPT) (L : PolyExpr) :
    PolyTimeComputable (padEncFun enc L) := by
  have ho : PolyTimeComputable fun z =>
      enc.output (NUPPT.layout (NUPPT.inParam z) (NUPPT.inArg z) [] (NUPPT.inCoins z)) :=
    enc.polyTimeComputable_output.comp (NUPPT.polyTimeComputable_layout
      NUPPT.polyTimeComputable_inParam NUPPT.polyTimeComputable_inArg
      (polyTimeComputable_const []) NUPPT.polyTimeComputable_inCoins)
  have h := ho.pairEncode ((polyTimeComputable_pairDropPoly .var).comp
    ((ho.pairEncode (polyTimeComputable_const [])).pairEncode
      ((polyTimeComputable_unaryPoly L).comp NUPPT.polyTimeComputable_inParam)))
  convert h using 1
  funext z
  simp [padEncFun, padCt, Function.comp_apply, length_pairEncode]

/-- The padded decryptor's string function on `⟨sk, w⟩`: `Dec ⟨sk, c⟩` if `w` is the canonical
padding of `c`, and `⊥` otherwise, here `true :: w`, one bit longer than the query. -/
def padDecFun (dec : List Bool → List Bool) (z : List Bool) : List Bool :=
  if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
  else true :: pairSndD z

/-- The padded decryptor decrypts the unpadded query when its canonical test passes and
returns `true :: pairSndD z` otherwise. -/
theorem padDecFun_eq (dec : List Bool → List Bool) (z : List Bool) :
    padDecFun dec z =
      if isPadded (pairSndD z) then dec (pairEncode (pairFstD z) (pairFstD (pairSndD z)))
      else true :: pairSndD z := rfl

/-- The padded decryptor is polynomial-time when `Dec` is. -/
theorem polyTimeComputable_padDecFun {dec : List Bool → List Bool}
    (hdec : PolyTimeComputable dec) : PolyTimeComputable (padDecFun dec) :=
  polyTimeComputable_ite (polyTimeComputable_isPadded.comp polyTimeComputable_pairSndD)
    (hdec.comp (polyTimeComputable_pairFstD.pairEncode
      (polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD)))
    ((polyTimeComputable_const [true]).append polyTimeComputable_pairSndD)

/-- The padded encryptor as a machine, with the coins of `Enc`. -/
noncomputable abbrev padEnc (enc : NUPPT) (L : PolyExpr) : NUPPT :=
  NUPPT.ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor uses the original encryptor's coin polynomial. -/
theorem padEnc_coins (enc : NUPPT) (L : PolyExpr) : (padEnc enc L).coins = enc.coins :=
  NUPPT.coins_ofPolyTimeUniform (polyTimeComputable_padEncFun enc L) enc.coins

/-- The padded encryptor pads the ciphertext of the uniform `Enc` with the same coin string,
read in `enc` through the public `padEnc_coins` identification. -/
theorem runAt_padEnc {enc : NUPPT} (henc : enc.Uniform) (L : PolyExpr) (n : ℕ) (y : List Bool)
    (r : (padEnc enc L).Coins n) : (padEnc enc L).runAt n y r =
      padCt (L.eval n) (enc.runAt n y (NUPPT.coinsCongr (padEnc_coins enc L) n r)) := by
  rw [NUPPT.runAt_eq, NUPPT.runAtL_ofPolyTimeUniform, henc.runAt_eq,
    NUPPT.coinsCongr_ofFn]
  simp only [padEncFun_eq, NUPPT.inParam_eq, NUPPT.inArg_eq, NUPPT.inCoins_eq,
    NUPPT.layout_eq, NUPPT.advInput_eq, pairFstD_pairEncode, pairSndD_pairEncode,
    List.length_replicate]

/-- The padded decryptor on a padding is `Dec`. -/
theorem padDecFun_padCt (dec : List Bool → List Bool) (sk c : List Bool) (L : ℕ) :
    padDecFun dec (pairEncode sk (padCt L c)) = dec (pairEncode sk c) := by
  simp [padDecFun, isPadded_padCt]

/-- The padded decryptor answers a non-canonical query `w` with a string of `|w| + 1` bits. -/
theorem padDecFun_of_not_isPadded (dec : List Bool → List Bool) (sk w : List Bool)
    (hw : isPadded w = false) : padDecFun dec (pairEncode sk w) = true :: w := by
  simp [padDecFun, hw]

/-! ### Fixed-length public-key schemes -/

/-- A **public-key scheme with fixed-length ciphertexts** [PS10, Definition 102.1]: `msgLen(n)`-bit
messages; `Gen(1^n) = ⟨pk, sk⟩`; `Enc_pk(m)` activated on `⟨pk, m⟩`, whose ciphertexts under
generated keys have `ctLen(n)` bits; a deterministic polynomial-time `Dec` on `⟨sk, c⟩`, with
`⊥` any output that decodes to no message; perfect correctness. -/
structure FixedLengthPKScheme where
  /-- The message length. -/
  msgLen : PolyExpr
  /-- The ciphertext length. -/
  ctLen : PolyExpr
  /-- The key generator. -/
  gen : NUPPT
  /-- The encryptor. -/
  enc : NUPPT
  /-- The decryptor. -/
  dec : List Bool → List Bool
  /-- `Gen` is a PPT. -/
  gen_uniform : gen.Uniform
  /-- `Enc` is a PPT. -/
  enc_uniform : enc.Uniform
  /-- `Dec` is polynomial-time. -/
  dec_poly : PolyTimeComputable dec
  /-- Perfect correctness. -/
  correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
    decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
      (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m
  /-- Ciphertexts under generated keys have `ctLen(n)` bits. -/
  enc_length : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
    (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length =
      ctLen.eval n

namespace FixedLengthPKScheme

/-- **The padded scheme**: a public-key scheme with ciphertexts padded to `L(n)` bits, given that
`L` bounds the honest ciphertexts (`2|c| + 2 ≤ L(n)`) and the message length (so that `⊥` on a
non-canonical `L(n)`-bit query, `|w| + 1` bits, decodes to no message). -/
noncomputable def ofPadded (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (_hmsg : ∀ n, msgLen.eval n ≤ L.eval n) : FixedLengthPKScheme where
  msgLen := msgLen
  ctLen := L
  gen := gen
  enc := padEnc enc L
  dec := padDecFun dec
  gen_uniform := gen_uniform
  enc_uniform := NUPPT.ofPolyTimeUniform_uniform _ _
  dec_poly := polyTimeComputable_padDecFun dec_poly
  correct := by
    intro n m rg re
    rw [runAt_padEnc enc_uniform, padDecFun_padCt]
    exact correct n m rg (NUPPT.coinsCongr (padEnc_coins enc L) n re)
  enc_length := by
    intro n rg m re
    rw [runAt_padEnc enc_uniform]
    exact length_padCt (hL n rg m (NUPPT.coinsCongr (padEnc_coins enc L) n re))

section PaddedReaders

variable (msgLen : PolyExpr) (gen enc : NUPPT) (dec : List Bool → List Bool)
    (gen_uniform : gen.Uniform) (enc_uniform : enc.Uniform) (dec_poly : PolyTimeComputable dec)
    (correct : ∀ n (m : Fin (msgLen.eval n) → Bool) (rg : gen.Coins n) (re : enc.Coins n),
      decodeFin _ (dec (pairEncode (pairSndD (gen.runAt n [] rg))
        (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re))) = some m)
    (L : PolyExpr)
    (hL : ∀ n (rg : gen.Coins n) (m : Fin (msgLen.eval n) → Bool) (re : enc.Coins n),
      2 * (enc.runAt n (pairEncode (pairFstD (gen.runAt n [] rg)) (List.ofFn m)) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, msgLen.eval n ≤ L.eval n)

/-- The padded constructor preserves the supplied message-length polynomial. -/
theorem ofPadded_msgLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).msgLen =
      msgLen := rfl

/-- The padded constructor's ciphertext-length polynomial is `L`. -/
theorem ofPadded_ctLen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).ctLen =
      L := rfl

/-- The padded constructor preserves the supplied key generator. -/
theorem ofPadded_gen :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).gen =
      gen := rfl

/-- The padded constructor uses `padEnc enc L` as its encryptor. -/
theorem ofPadded_enc :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).enc =
      padEnc enc L := rfl

/-- The padded constructor uses `padDecFun dec` as its decryptor. -/
theorem ofPadded_dec :
    (ofPadded msgLen gen enc dec gen_uniform enc_uniform dec_poly correct L hL hmsg).dec =
      padDecFun dec := rfl

end PaddedReaders

end FixedLengthPKScheme

/-- **A ch. 2–4 public-key scheme, padded** to `L(n)`-bit ciphertexts. -/
noncomputable def _root_.TCSlib.Cryptography.PublicKeyScheme.padded (S : PublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded .var S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n m rg re => S.correct n m rg re) L hL hmsg

section PublicKeyPaddedReaders

variable (S : PublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
        + 2 ≤ L.eval n)
    (hmsg : ∀ n, n ≤ L.eval n)

/-- Padding a public-key scheme preserves its message-length polynomial `PolyExpr.var`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.var := rfl

/-- The padded public-key scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded public-key scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded public-key scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

/-- **The padded encryptor pads the original encryptor's output**, the coins read as a list:
`Enc'(1^n, y; r) = padCt L(n) (Enc(1^n, y; ⟦r⟧))` (`runAt_padEnc`, `coinsCongr_ofFn`). -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc_runAt (n : ℕ) (y : List Bool)
    (r : (S.padded L hL hmsg).enc.Coins n) :
    (S.padded L hL hmsg).enc.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
  have key : ∀ E : NUPPT, E = padEnc S.enc L → ∀ r : E.Coins n,
      E.runAt n y r = padCt (L.eval n) (S.enc.runAtL n y (List.ofFn r)) := by
    rintro E rfl r
    rw [runAt_padEnc S.enc_uniform L n y r, NUPPT.runAt_eq, NUPPT.coinsCongr_ofFn]
  exact key _ (PublicKeyScheme.padded_enc S L hL hmsg) r

/-- The padded encryptor keeps the coins: `S.enc.coins = (S.padded L hL hmsg).enc.coins`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.padded_enc_coins :
    S.enc.coins = (S.padded L hL hmsg).enc.coins := by
  rw [PublicKeyScheme.padded_enc, padEnc_coins]

end PublicKeyPaddedReaders

/-- **A ch. 2–4 single-bit public-key scheme, padded** to `L(n)`-bit ciphertexts: one-bit
messages, `Enc` activated on `⟨pk, [b]⟩`. -/
noncomputable def _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded (S : BitPublicKeyScheme)
    (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n) : FixedLengthPKScheme :=
  .ofPadded (.const 1) S.gen S.enc S.dec S.gen_uniform S.enc_uniform S.dec_poly
    (fun n (m : Fin 1 → Bool) rg re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm, S.correct n (m 0) rg re, ← hm, decodeFin_ofFn])
    L
    (fun n rg (m : Fin 1 → Bool) re => by
      have hm : List.ofFn m = [m 0] := by simp
      rw [hm]
      exact hL n rg (m 0) re)
    hmsg

section BitPublicKeyPaddedReaders

variable (S : BitPublicKeyScheme) (L : PolyExpr)
    (hL : ∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
      2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
        ≤ L.eval n)
    (hmsg : ∀ n, 1 ≤ L.eval n)

/-- Padding a single-bit public-key scheme preserves its constant one-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_msgLen :
    (S.padded L hL hmsg).msgLen = PolyExpr.const 1 := rfl

/-- The padded single-bit scheme's ciphertext-length polynomial is `L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_ctLen :
    (S.padded L hL hmsg).ctLen = L := rfl

/-- Padding a single-bit public-key scheme preserves its key generator. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_gen :
    (S.padded L hL hmsg).gen = S.gen := rfl

/-- The padded single-bit scheme encrypts with `padEnc S.enc L`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_enc :
    (S.padded L hL hmsg).enc = padEnc S.enc L := rfl

/-- The padded single-bit scheme decrypts with `padDecFun S.dec`. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded_dec :
    (S.padded L hL hmsg).dec = padDecFun S.dec := rfl

end BitPublicKeyPaddedReaders

/-- **A padding bound exists** for every ch. 2–4 public-key scheme, from the time bounds of
`Gen` and `Enc` (`NUPPT.length_runAt_le_runLenPoly`): `|pk| ≤ Q₁(n)`, the input `⟨pk, m⟩` has at
most `2Q₁(n) + 2 + n` bits, and the ciphertext at most `Q₂(n)`; `L = 2Q₂ + 2 + n` works.

**Proof sketch.** Bound the generator's output by its running-time polynomial, which also
bounds its public-key projection. The pair-encoding length formula then bounds the encryptor's
input by `2Q₁(n) + 2 + n`. Applying the encryptor's output-length bound to this input gives
`Q₂(n)`. Choose `L(n) = 2Q₂(n) + 2 + n`: it covers the ciphertext's pair-encoding overhead and
is at least the message length `n`. -/
theorem _root_.TCSlib.Cryptography.PublicKeyScheme.exists_padBound (S : PublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (m : Fin n → Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)) re).length
          + 2 ≤ L.eval n) ∧ ∀ n, n ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (m : Fin n → Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) (List.ofFn m)).length ≤
        (PolyExpr.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var).eval
          n := by
    intro n rg m
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_ofFn, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  refine ⟨.add (.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 2)) .var))) (.const 2))
      .var, fun n rg m re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg m) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]
    omega

/-- **A padding bound exists** for every ch. 2–4 single-bit public-key scheme (as for
`PublicKeyScheme.exists_padBound`).

**Proof sketch.** The generator's output-length bound also bounds the public key by `Q₁(n)`.
Pairing that key with one bit gives an encryptor input of at most `2Q₁(n) + 3` bits. Its
running-time bound therefore supplies a ciphertext-length polynomial `Q₂(n)`. The polynomial
`L(n) = 2Q₂(n) + 2` covers the ciphertext encoding and is at least one, as required for the
single-bit message length. -/
theorem _root_.TCSlib.Cryptography.BitPublicKeyScheme.exists_padBound (S : BitPublicKeyScheme) :
    ∃ L : PolyExpr,
      (∀ n (rg : S.gen.Coins n) (b : Bool) (re : S.enc.Coins n),
        2 * (S.enc.runAt n (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]) re).length + 2
          ≤ L.eval n) ∧ ∀ n, 1 ≤ L.eval n := by
  have hY : ∀ n (rg : S.gen.Coins n) (b : Bool),
      (pairEncode (pairFstD (S.gen.runAt n [] rg)) [b]).length ≤
        (PolyExpr.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)).eval n := by
    intro n rg b
    have h₀ := length_pairFstD_le (S.gen.runAt n [] rg)
    have h₁ := S.gen.length_runAt_le_runLenPoly (Y := .const 0) n (y := []) (by simp) rg
    simp only [length_pairEncode, List.length_singleton, PolyExpr.eval_add, PolyExpr.eval_mul,
      PolyExpr.eval_const]
    omega
  refine ⟨.add (.mul (.const 2) (S.enc.runLenPoly
    (.add (.mul (.const 2) (S.gen.runLenPoly (.const 0))) (.const 3)))) (.const 2),
      fun n rg b re => ?_, fun n => ?_⟩
  · have h₂ := S.enc.length_runAt_le_runLenPoly n (hY n rg b) re
    simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  · simp only [PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega

/-! ### The experiment of Definition 171.5 -/

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-- The query lengths of the two oracles `Dec` and `Challenge` at parameter `n`. -/
def inLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => S.msgLen.eval n + S.msgLen.eval n

/-- Decryption queries have the scheme's ciphertext length. -/
theorem inLens_zero (n : ℕ) : S.inLens n 0 = S.ctLen.eval n := rfl

/-- Challenge queries contain two messages of the scheme's message length. -/
theorem inLens_one (n : ℕ) : S.inLens n 1 = S.msgLen.eval n + S.msgLen.eval n := rfl

/-- The answer lengths: `Dec` answers a validity flag and a message; `Challenge` a ciphertext. -/
def outLens (n : ℕ) : Fin 2 → ℕ
  | 0 => S.msgLen.eval n + 1
  | 1 => S.ctLen.eval n

/-- Decryption answers contain a validity bit followed by one message. -/
theorem outLens_zero (n : ℕ) : S.outLens n 0 = S.msgLen.eval n + 1 := rfl

/-- Challenge answers have the scheme's ciphertext length. -/
theorem outLens_one (n : ℕ) : S.outLens n 1 = S.ctLen.eval n := rfl

/-- The two oracles of the experiment at parameter `n`. -/
abbrev indSpec (n : ℕ) : OracleSpec (Fin 2) := bitSpec (S.inLens n) (S.outLens n)

/-- The public-key IND oracle specification is the bit specification at the scheme's query
and answer lengths. -/
theorem indSpec_eq (n : ℕ) : S.indSpec n = bitSpec (S.inLens n) (S.outLens n) := rfl

/-- Oracle `i` accepts bit strings of length `S.inLens n i`. -/
theorem indSpec_dom (n : ℕ) (i : Fin 2) :
    (S.indSpec n).dom i = (Fin (S.inLens n i) → Bool) :=
  bitSpec_dom (S.inLens n) (S.outLens n) i

/-- The decryption oracle accepts a ciphertext at the scheme's encoded width. -/
theorem indSpec_decDom (n : ℕ) : (S.indSpec n).dom 0 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_dom, S.inLens_zero]

/-- Oracle `i` returns bit strings of length `S.outLens n i`. -/
theorem indSpec_rng (n : ℕ) (i : Fin 2) :
    (S.indSpec n).rng i = (Fin (S.outLens n i) → Bool) :=
  bitSpec_rng (S.inLens n) (S.outLens n) i

/-- **The oracles of `Ind_b`** at parameter `n`, for the keys `pk`, `sk`; the state is the
challenge, once asked.
- `Dec` answers `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is not the challenge, and
  `⊥` (all `false`) otherwise; an output that decodes to no message is `⊥` as well.
- `Challenge` answers `Enc_pk(m_b)` on `⟨m₀, m₁⟩` the first time it is asked, and records it;
  later it repeats the recorded challenge. -/
noncomputable def indImpl (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool) :
    QueryImpl (S.indSpec n) (Option (Fin (S.ctLen.eval n) → Bool)) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
      .pure (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
    else .pure (zeroBits _, s)
  | 1, mm, s =>
    match s with
    | some c => .pure (c, s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c)

/-- A decryption query checks oracle availability and refuses the recorded challenge;
otherwise it returns the decoded plaintext with its validity flag, preserving the state. -/
theorem indImpl_dec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some c) then
        .pure (FixedLengthScheme.decAnswer
          (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
      else .pure (zeroBits _, s) := rfl

/-- The first challenge query encrypts the selected message half using fresh coins and
records the padded ciphertext. -/
theorem indImpl_challenge_none (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n (pairEncode pk (List.ofFn
          (if b then (FixedLengthScheme.splitHalf mm).2 else (FixedLengthScheme.splitHalf mm).1)))
          r)
        .pure (c, some c) := rfl

/-- A repeated challenge query returns the recorded ciphertext and preserves it as state. -/
theorem indImpl_challenge_repeat (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (c, some c) := rfl

/-- The decryption equation on the query specification's type. Read the ciphertext through
the width equality before checking challenge refusal and decrypting. -/
theorem indImpl_dec_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec atk b n pk sk c s

/-- The decryption oracle answers a validity bit followed by one message:
`(S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool)`. -/
theorem indSpec_decRng (n : ℕ) : (S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool) := by
  rw [S.indSpec_rng, S.outLens_zero]

/-- `indImpl_dec_onSpec` with the answer cast through `indSpec_decRng`: for `c' = cast _ c`,
`S.indImpl atk b n pk sk 0 c s = if decOpen atk s.isSome && s ≠ some c' then
pure (cast _ (decAnswer (decodeFin _ (Dec ⟨sk, c'⟩))), s) else pure (zeroBits _, s)`. -/
theorem indImpl_dec_onSpec_cast (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (cast (S.indSpec_decRng n).symm (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c)))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec_onSpec atk b n pk sk c s

/-- The challenge oracle returns a ciphertext at the scheme's encoded width. -/
theorem indSpec_challengeRng (n : ℕ) :
    (S.indSpec n).rng 1 = (Fin (S.ctLen.eval n) → Bool) := by
  rw [S.indSpec_rng, S.outLens_one]

/-- A challenge query contains two messages at the scheme's message width. -/
theorem indSpec_challengeDom (n : ℕ) :
    (S.indSpec n).dom 1 = (Fin (S.msgLen.eval n + S.msgLen.eval n) → Bool) := by
  rw [S.indSpec_dom, S.inLens_one]

/-- The fresh challenge equation on the query specification's type. Draw new encryption
coins, encrypt the selected half of the query, and record the resulting ciphertext. -/
theorem indImpl_challenge_none_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : (S.indSpec n).dom 1) :
    S.indImpl atk b n pk sk 1 mm none =
      (ProbComp.sample (S.enc.Coins n)).bind fun r =>
        let halves := FixedLengthScheme.splitHalf (cast (S.indSpec_challengeDom n) mm)
        let c := padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode pk (List.ofFn (if b then halves.2 else halves.1))) r)
        .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_none atk b n pk sk mm

/-- Repeating the challenge preserves the previous state for a query of the specification's
type. -/
theorem indImpl_challenge_repeat_onSpec (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (mm : (S.indSpec n).dom 1) (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl atk b n pk sk 1 mm (some c) = .pure (cast (S.indSpec_challengeRng n).symm c, some c) := by
  simpa only [cast_eq] using S.indImpl_challenge_repeat atk b n pk sk mm c

/-- Under CPA, `Dec` never answers. -/
theorem indImpl_dec_cpa (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl .cpa b n pk sk 0 c s = .pure (zeroBits _, s) := by
  simp [indImpl, FixedLengthScheme.decOpen_cpa]

/-- Under CCA2, `Dec` refuses the challenge. -/
theorem indImpl_dec_cca2_challenge (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : Fin (S.ctLen.eval n) → Bool) :
    S.indImpl .cca2 b n pk sk 0 c (some c) = .pure (zeroBits _, some c) := by
  simp [indImpl, FixedLengthScheme.decOpen_cca2]

/-- The codec of the adversary: the two oracles, and a one-bit final output. -/
def indCodec (n : ℕ) : MachineCodec (S.indSpec n) (Fin 1 → Bool) :=
  bitCodec (S.inLens n) (S.outLens n) 1

/-- The public-key IND codec decodes a move with the bit decoder at the scheme's oracle
lengths and a one-bit final output. -/
theorem indCodec_decodeMove (n : ℕ) (w : List Bool) :
    (S.indCodec n).decodeMove w = decodeBitMove (S.inLens n) (S.outLens n) 1 w :=
  bitCodec_decodeMove (S.inLens n) (S.outLens n) 1 w

/-- The public-key IND codec encodes an entry by pairing the unary oracle index with its
query and answer strings. -/
theorem indCodec_encodeEntry (n : ℕ)
    (e : Σ i, (S.indSpec n).dom i × (S.indSpec n).rng i) :
    (S.indCodec n).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.inLens n) (S.outLens n) 1 e

/-- The public-key IND codec returns the false one-bit result on timeout. -/
theorem indCodec_timeout (n : ℕ) : (S.indCodec n).timeout = zeroBits 1 :=
  bitCodec_timeout (S.inLens n) (S.outLens n) 1

/-- The adversary codec is a bit codec: `S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1`. -/
theorem indCodec_eq_bitCodec (n : ℕ) : S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl

/-- **The experiment `Ind_b(Π, A, n)`** [PS10, Definition 171.5] for the attack `atk`, with query
budget `q`: sample `(pk, sk) ← Gen(1^n)` and `A`'s coins, run `A` on `pk` against the oracles
from the unchallenged state, and output its bit. -/
noncomputable def indGame (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (A.Coins n)).bind fun r =>
  (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)))
      (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
    fun res => .pure (res.1 0)

/-- The public-key IND game samples key-generation and adversary coins, simulates the
oracles on the public-key input from the unchallenged state, and returns the final bit. -/
theorem indGame_eq (atk : Attack) (A : NUPPT) (q : ℕ) (b : Bool) (n : ℕ) :
    S.indGame atk A q b n =
      (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
      (ProbComp.sample (A.Coins n)).bind fun r =>
      (simulate (S.indImpl atk b n (pairFstD (S.gen.runAt n [] rg))
          (pairSndD (S.gen.runAt n [] rg)))
        (A.toCompOn (S.indCodec n) n q (pairFstD (S.gen.runAt n [] rg)) r) none).bind
        fun res => .pure (res.1 0) := rfl

/-- **CPA, CCA1 or CCA2 security of a public-key scheme** [PS10, Definition 171.5]: for every
non-uniform PPT `A` and every polynomial query budget, `A`'s advantage between `Ind_0` and
`Ind_1` is negligible. -/
def INDSecure (atk : Attack) : Prop :=
  ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
    ∀ n, advantage (S.indGame atk A (q.eval n) false n) (S.indGame atk A (q.eval n) true n) ≤ ε n

/-- Public-key IND security is exactly negligible advantage for every non-uniform PPT
adversary and polynomial query budget, uniformly over the security parameter. -/
theorem INDSecure_iff (atk : Attack) :
    S.INDSecure atk ↔ ∀ (A : NUPPT) (q : PolyExpr), ∃ ε : ℕ → ℝ, Negligible ε ∧
      ∀ n, advantage (S.indGame atk A (q.eval n) false n)
        (S.indGame atk A (q.eval n) true n) ≤ ε n := Iff.rfl

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability
