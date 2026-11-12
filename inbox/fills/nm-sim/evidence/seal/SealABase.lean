/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import Mathlib.Tactic.Simps.Basic

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Simulation-based non-malleability (statement phase)

[PS10, Definition 173.7 and Theorem 174.8], in the form of [PSV07] (ruling of 2026-11-05: the
non-malleability notions of §7.1.5–7.1.6 follow Pass, shelat and Vaikuntanathan).

**Why not the source's form.** As written, Theorem 174.8 is false (inventory Thm-174.8).
- Definition 173.7's simulator `S(1^n, z)` gets no public key. An adversary that outputs a fresh
  `Enc_pk(0^n)` hits the relation `R(m) = {0^n}` with probability 1, while a simulator without
  `pk` produces a ciphertext that decrypts to `0^n` under a fresh key only with the probability
  of guessing one.
- The quantifiers of Definitions 172.6 and 173.7 do not line up: adaptive `m₀, m₁` in one, a
  fixed `m` in the other.

**The form taken: SIM-NME′ at one message** [PSV07, Definition 1, with `ℓ = 1`; "single-message
security" there].
- *Real.* `(pk, sk) ← Gen(1^n)`; `(M, s) ← A₁^{O₁}(pk)`; `m ← M`; `y ← Enc_pk(m)`;
  `((c₁, …, c_r), σ) ← A₂^{O₂}(y, h(m), s)`; output `(M, m, (d₁, …, d_r), σ)` with
  `d_i = COPY` if `c_i = y` and `d_i = Dec_sk(c_i)` otherwise (possibly `⊥`: invalid ciphertexts
  are allowed, the "′" of [PSV07]).
- *Ideal.* `(pk, sk) ← Gen(1^n)`; `(M, s) ← S₁(pk)`; `m ← M`; `((c₁, …, c_r), σ) ← S₂(h(m), s)`;
  output `(M, m, (d₁, …, d_r), σ)` with `d_i = COPY` if `c_i = COPY` and `Dec_sk(c_i)` otherwise.
- *Security.* For every history function `h`, every adversary `A` and all polynomials `r`, there
  is a simulator `S` whose experiment no distinguisher tells from `A`'s. [PSV07] replaces the
  relations `R` of [PS10] and [DDN00] by distinguishers ("any p.p.t. distinguisher can be
  described as a p.p.t. relation and vice versa", remarks after Definition 2).

**The encoding.**
- *Phases and oracles* are those of Definition 171.5: the challenge query separates `A₁` from
  `A₂`, and `Dec` answers per the attack (`decOpen`), refusing the challenge.
- *The sampler.* [PSV07]'s `A₁` outputs a machine `M`. Here a sampler `M` (a machine with a
  history function, `MsgSampler`) is quantified together with `A`, and `A₁` outputs a parameter
  `a`, with `m = M(a)` read at `msgLen(n)` bits. The output carries `a` in place of `M`'s
  description. With `M` a universal clocked machine this is [PSV07]'s form, and the fixed
  lengths make every sampler valid in [PSV07]'s sense.
- *The simulator* is one oracle machine on `pk`. Its single query `a` is answered by `h(m)`,
  where `m = M(a)` is drawn by the experiment: `S₁` is its run up to the query, `S₂` the rest. It
  has no `Dec` oracle under any attack, as in [PSV07]. Each of its `r` outputs is a `COPY` flag
  and a ciphertext.
- *No challenge.* If the machine never queries, its parameter is `0^{pl(n)}` and `m = M(0^{pl(n)})`
  (in both experiments).

**Theorem 174.8.** [PSV07] proves that SIM-NME′ and IND-NME′ (Definition 172.6 at many messages)
coincide **under CPA** (its Theorem 3), and that SIM-NME′ is **strictly stronger under CCA1 and
CCA2**, even at one message (its Theorem 4). It always implies IND-NME′ (its Corollary 1). So
Theorem 174.8 is stated under CPA, with the implication SIM ⇒ IND for every attack. [PSV07]
defers both proofs to its full version; the sketches below are the maintainer's.

## Main definitions

* `MsgSampler`: a message sampler with a history function.
* `FixedLengthPKScheme.snmReal`, `FixedLengthPKScheme.snmIdeal`: the two experiments.
* `FixedLengthPKScheme.SimNMSecure`: [PS10, Definition 173.7] as [PSV07, Definition 1].

## Main results

* `FixedLengthPKScheme.nmSecure_of_simNMSecure` (stated; a `sorry` under its sketch):
  SIM ⇒ IND for every attack [PSV07, Corollary 1].
* `FixedLengthPKScheme.simNMSecure_of_nmSecure_cpa` (stated; a `sorry` under its sketch):
  IND ⇒ SIM under CPA [PSV07, Theorem 3].
* `FixedLengthPKScheme.simNMSecure_cpa_iff_nmSecure_cpa`: Theorem 174.8 under CPA, from the two.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  §7.1.6, Definition 173.7 and Theorem 174.8 (book pp. 173–174).
* [PSV07] R. Pass, a. shelat, V. Vaikuntanathan, *Relations among notions of non-malleability for
  encryption*, ASIACRYPT 2007, LNCS 4833, pp. 519–535: Definitions 1–4, Theorems 3 and 4,
  Corollary 1.
* [PSV06] R. Pass, a. shelat, V. Vaikuntanathan, *Construction of a non-malleable encryption
  scheme from any semantically secure one*, CRYPTO 2006, LNCS 4117, pp. 271–289: Definition 3.
* [DDN00] D. Dolev, C. Dwork, M. Naor, *Nonmalleable cryptography*, SIAM J. Comput. 30(2), 2000
  (cited through [PSV07]).
-/

namespace TCSlib.Cryptography.Composability

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! Seal A of the nm-sim fill: a verbatim copy of `scratch/seal/BaseOwned.lean`, with every seal candidate of
its full TCSlib import closure (1283 definitions, `PolyExpr.eval` exempt as notation) irreducible from here on. -/
attribute [local irreducible] _root_.BoolCircuit.DAGCircuit.IsFaninTwo _root_.BoolCircuit.DAGCircuit.IsWellFormed _root_.BoolCircuit.DAGCircuit.binarize _root_.BoolCircuit.DAGCircuit.deMorgan _root_.BoolCircuit.DAGCircuit.depth _root_.BoolCircuit.DAGCircuit.depthAt _root_.BoolCircuit.DAGCircuit.depths _root_.BoolCircuit.DAGCircuit.eval _root_.BoolCircuit.DAGCircuit.layerGate _root_.BoolCircuit.DAGCircuit.layerNodes _root_.BoolCircuit.DAGCircuit.ofNode _root_.BoolCircuit.DAGCircuit.rewrite _root_.BoolCircuit.DAGCircuit.size _root_.BoolCircuit.DAGCircuit.toLayered _root_.BoolCircuit.DAGCircuit.toLayered_evalNode.match_1_1 _root_.BoolCircuit.DAGCircuit.toNode _root_.BoolCircuit.DAGCircuit.toTree _root_.BoolCircuit.DAGCircuit.unfoldVertex_depth_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_eval.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_maxFanin_le.match_1_1 _root_.BoolCircuit.DAGCircuit.unfoldVertex_size_le.match_1_1 _root_.BoolCircuit.DAGCircuit.values _root_.BoolCircuit.DAGCircuitFamily.Accepts _root_.BoolCircuit.DAGCircuitFamily.HasFaninTwo _root_.BoolCircuit.DAGCircuitFamily.HasPolylogDepth _root_.BoolCircuit.DAGCircuitFamily.IsPolySize _root_.BoolCircuit.DAGCircuitFamily.IsWellFormed _root_.BoolCircuit.DAGCircuitFamily.language _root_.BoolCircuit.DAGGate.FaninTwo _root_.BoolCircuit.DAGGate.NoOr _root_.BoolCircuit.DAGGate.WellFormed _root_.BoolCircuit.DAGGate.depth _root_.BoolCircuit.DAGGate.eval _root_.BoolCircuit.DAGGate.remap _root_.BoolCircuit.GadgetCorrect _root_.BoolCircuit.GateKind.enumList _root_.BoolCircuit.GateKind.ofNat _root_.BoolCircuit.GateKind.op _root_.BoolCircuit.GateKind.op.match_1 _root_.BoolCircuit.GateShape.eval _root_.BoolCircuit.GateShape.eval.match_1 _root_.BoolCircuit.GatesAcyclic _root_.BoolCircuit.LayeredCircuit.Gate.eval _root_.BoolCircuit.LayeredCircuit.IsAndOrGate _root_.BoolCircuit.LayeredCircuit.eval _root_.BoolCircuit.LayeredCircuit.evalNode _root_.BoolCircuit.LayeredCircuit.evalNode.match_1 _root_.BoolCircuit.LayeredCircuit.eval₁ _root_.BoolCircuit.LayeredCircuit.gatesUpTo _root_.BoolCircuit.LayeredCircuit.gatesUpTo.match_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_acyclic.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_mono.match_1_1 _root_.BoolCircuit.LayeredCircuit.gatesUpTo_wellFormed.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerEnum _root_.BoolCircuit.LayeredCircuit.layerGate _root_.BoolCircuit.LayeredCircuit.layerGate.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex _root_.BoolCircuit.LayeredCircuit.layerVertex.match_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_lt.match_1_1 _root_.BoolCircuit.LayeredCircuit.layerVertex_value.match_1_1 _root_.BoolCircuit.LayeredCircuit.length_gatesUpTo.match_1_1 _root_.BoolCircuit.LayeredCircuit.offset _root_.BoolCircuit.LayeredCircuit.onlyUsesGates _root_.BoolCircuit.LayeredCircuit.size _root_.BoolCircuit.LayeredCircuit.succCard _root_.BoolCircuit.LayeredCircuit.toDAG _root_.BoolCircuit.LayeredCircuit.toTreeCircuit _root_.BoolCircuit.LayeredCircuitFamily.Accepts _root_.BoolCircuit.LayeredCircuitFamily.IsPolySize _root_.BoolCircuit.LayeredCircuitFamily.OnlyUsesGates _root_.BoolCircuit.LayeredCircuitFamily.language _root_.BoolCircuit.LayeredPPoly _root_.BoolCircuit.Lit.eval _root_.BoolCircuit.NAndCircuit.constTrue _root_.BoolCircuit.NAndCircuit.eval.match_1 _root_.BoolCircuit.NAndCircuit.litCount.match_1 _root_.BoolCircuit.NAndCircuit.ofVar _root_.BoolCircuit.NOrCircuit.constFalse _root_.BoolCircuit.NOrCircuit.eval.match_1 _root_.BoolCircuit.NOrCircuit.litCount.match_1 _root_.BoolCircuit.NOrCircuit.ofVar _root_.BoolCircuit.PPoly _root_.BoolCircuit.TreeCircuit.depth_le_maxDepth.match_1_1 _root_.BoolCircuit.TreeCircuit.eval.match_1 _root_.BoolCircuit.TreeCircuit.ind.match_1_1 _root_.BoolCircuit.TreeCircuit.length_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxDepth _root_.BoolCircuit.TreeCircuit.maxFaninL _root_.BoolCircuit.TreeCircuit.maxFaninL_le_sumSize.match_1_1 _root_.BoolCircuit.TreeCircuit.maxFanin_le_maxFaninL.match_1_1 _root_.BoolCircuit.TreeCircuit.sumSize _root_.BoolCircuit.TreeCircuit.toDAG _root_.BoolCircuit.TreeCircuit.toLayered _root_.BoolCircuit.TreeCircuit.toLayeredWrapper _root_.BoolCircuit.TreeCircuit.toNAnd.match_1 _root_.BoolCircuit.TreeCircuit.toNOr.match_1 _root_.BoolCircuit.allOnesCircuit _root_.BoolCircuit.allOnesCircuit.match_1 _root_.BoolCircuit.allOnesFamily _root_.BoolCircuit.andGateOp _root_.BoolCircuit.binarizeGadget _root_.BoolCircuit.binarizeGadget.match_1 _root_.BoolCircuit.binarizeGadget_correct.match_1_1 _root_.BoolCircuit.compileTree _root_.BoolCircuit.compileTree.match_1 _root_.BoolCircuit.compileTrees _root_.BoolCircuit.compileTrees.match_1 _root_.BoolCircuit.compileTrees_spec.match_1_1 _root_.BoolCircuit.constCircuit _root_.BoolCircuit.constGate _root_.BoolCircuit.deMorganGadget _root_.BoolCircuit.deMorganGadget.match_1 _root_.BoolCircuit.deMorganGadget_correct.match_1_1 _root_.BoolCircuit.decodeNat _root_.BoolCircuit.decodeNat.match_1 _root_.BoolCircuit.emitNots _root_.BoolCircuit.emitNots.match_1 _root_.BoolCircuit.emitNots_spec.match_1_1 _root_.BoolCircuit.emitTree.match_1 _root_.BoolCircuit.emitTree_spec.match_1_1 _root_.BoolCircuit.encodeNat _root_.BoolCircuit.gateShape _root_.BoolCircuit.instDecidableEqDAGGate.decEq _root_.BoolCircuit.instDecidableEqDAGGate.decEq.match_1 _root_.BoolCircuit.instDecidableEqLit.decEq _root_.BoolCircuit.instDecidableEqLit.decEq.match_1 _root_.BoolCircuit.instHashableLit.hash _root_.BoolCircuit.instHashableLit.hash.match_1 _root_.BoolCircuit.instReprDAGGate.repr _root_.BoolCircuit.instReprGateKind.repr _root_.BoolCircuit.instReprGateKind.repr.match_1 _root_.BoolCircuit.instReprLit.repr _root_.BoolCircuit.instReprTreeCircuit.repr.match_1 _root_.BoolCircuit.layerGateOf _root_.BoolCircuit.layerGateOf.match_1 _root_.BoolCircuit.nodeKind _root_.BoolCircuit.rewriteGates _root_.BoolCircuit.rewriteStep _root_.BoolCircuit.runWith _root_.BoolCircuit.stdGateOps _root_.BoolCircuit.treeCost _root_.BoolCircuit.unfoldGate _root_.BoolCircuit.unfoldGate.match_1 _root_.BoolCircuit.unfoldGate_eval.match_1_10 _root_.BoolCircuit.unfoldGate_eval.match_1_12 _root_.BoolCircuit.unfoldGate_eval.match_1_4 _root_.BoolCircuit.unfoldGate_eval.match_1_6 _root_.BoolCircuit.unfoldVertex _root_.BoolCircuit.unfoldVertex.match_1 _root_.BoolCircuit.vertexDepth _root_.BoolCircuit.vertexValue _root_.Complexity.BinArith.DivInv _root_.Complexity.BinArith.MulInv _root_.Complexity.BinArith.SlotsLe _root_.Complexity.BinArith.add _root_.Complexity.BinArith.beq _root_.Complexity.BinArith.borrow _root_.Complexity.BinArith.carry _root_.Complexity.BinArith.chunkList _root_.Complexity.BinArith.chunkW _root_.Complexity.BinArith.countW _root_.Complexity.BinArith.div _root_.Complexity.BinArith.divInit _root_.Complexity.BinArith.divLoop _root_.Complexity.BinArith.divStep _root_.Complexity.BinArith.encWords _root_.Complexity.BinArith.eqW _root_.Complexity.BinArith.forLoop _root_.Complexity.BinArith.forStep _root_.Complexity.BinArith.getW _root_.Complexity.BinArith.guardLoop _root_.Complexity.BinArith.guardNxt _root_.Complexity.BinArith.hasFalse _root_.Complexity.BinArith.le _root_.Complexity.BinArith.lt _root_.Complexity.BinArith.mapW _root_.Complexity.BinArith.mod _root_.Complexity.BinArith.mul _root_.Complexity.BinArith.mulInit _root_.Complexity.BinArith.mulStep _root_.Complexity.BinArith.mulU _root_.Complexity.BinArith.padZip _root_.Complexity.BinArith.padZip.match_1 _root_.Complexity.BinArith.pairO _root_.Complexity.BinArith.pairδ _root_.Complexity.BinArith.pairδ.match_1 _root_.Complexity.BinArith.revStep _root_.Complexity.BinArith.serialOut _root_.Complexity.BinArith.serialOut.match_1 _root_.Complexity.BinArith.serialState _root_.Complexity.BinArith.sub _root_.Complexity.BinArith.sumBit _root_.Complexity.BinArith.uHead _root_.Complexity.BinArith.uRest _root_.Complexity.BinArith.zipWithW _root_.Complexity.BlockLoop.emit _root_.Complexity.BlockLoop.step _root_.Complexity.CounterProg.Goes _root_.Complexity.CounterProg.Goes.mono.match_1_1 _root_.Complexity.CounterProg.LinE.val _root_.Complexity.CounterProg.MOp.exec _root_.Complexity.CounterProg.MOp.exec.match_1 _root_.Complexity.CounterProg.St.ext.match_1 _root_.Complexity.CounterProg.TSt.proxyTypeEquiv _root_.Complexity.CounterProg.act _root_.Complexity.CounterProg.bitsOps _root_.Complexity.CounterProg.ctl _root_.Complexity.CounterProg.enc _root_.Complexity.CounterProg.init _root_.Complexity.CounterProg.instDecidableEqTSt.decEq _root_.Complexity.CounterProg.instDecidableEqTSt.decEq.match_1 _root_.Complexity.CounterProg.instFintypeTSt.match_3 _root_.Complexity.CounterProg.instFintypeTSt.match_5 _root_.Complexity.CounterProg.linOps _root_.Complexity.CounterProg.run _root_.Complexity.CounterProg.shiftInput _root_.Complexity.CounterProg.step _root_.Complexity.CounterProg.step.match_1 _root_.Complexity.CounterProg.step.match_3 _root_.Complexity.CounterProg.step.match_5 _root_.Complexity.CounterProg.tmplInstr _root_.Complexity.CounterProg.tmplInstr.match_1 _root_.Complexity.CounterProg.toTM _root_.Complexity.CounterProg.tr _root_.Complexity.CounterProg.tr.match_1 _root_.Complexity.DTIME _root_.Complexity.DTIMEAdvice _root_.Complexity.IterateFind.copyTM _root_.Complexity.IterateFind.copyTM.match_1 _root_.Complexity.IterateFind.find?_congr_of_mem.match_1_1 _root_.Complexity.IterateFind.hostCtrl _root_.Complexity.IterateFind.hostRet _root_.Complexity.IterateFind.polyTimeComputable_find.match_1 _root_.Complexity.IterateFind.polyTimeComputable_find.match_1_1 _root_.Complexity.IterateFind.step _root_.Complexity.LogProg.bitsVal _root_.Complexity.LogProg.bitsVal.match_1 _root_.Complexity.LogProg.eq_of_bitsVal_eq.match_1_1 _root_.Complexity.LogProg.incW _root_.Complexity.LogProg.incW.match_1 _root_.Complexity.LoopInv _root_.Complexity.NP _root_.Complexity.NUPPT.Computes _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.adviceLen _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.combineAdvice _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.inverterLit _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.preComp _root_.Complexity.NUPPT.preComp_coinsEquiv _root_.Complexity.NUPPT.preFun _root_.Complexity.NUPPT.precomp _root_.Complexity.NUPPT.precomp_coinsEquiv _root_.Complexity.NUPPT.predictor _root_.Complexity.NUPPT.reparam _root_.Complexity.NUPPT.reparamCoins _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.runLenPoly _root_.Complexity.NUPPT.runLit _root_.Complexity.NUPPT.timeBound _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.NUPPT.withIndexParam _root_.Complexity.NUPPT.withIndexParam_coinsEquiv _root_.Complexity.NUPPT.wrap _root_.Complexity.NUPPT.wrapCoinsEquiv _root_.Complexity.NUPPT.wrapFun _root_.Complexity.P _root_.Complexity.PAdvicePoly _root_.Complexity.PPT _root_.Complexity.PPT.ofPolyTime _root_.Complexity.PPT.toNUPPT _root_.Complexity.PolyBound _root_.Complexity.PolyExpr.eval.match_1 _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyExpr.subst _root_.Complexity.PolyExpr.subst.match_1 _root_.Complexity.PolyHierarchy.UnaryPT _root_.Complexity.PolyHierarchy.padDecode _root_.Complexity.PolyHierarchy.padDecode.match_1 _root_.Complexity.PolyHierarchy.polyTimeComputable_padDecode.match_1_1 _root_.Complexity.PolyHierarchy.tupleDecode _root_.Complexity.PolyHierarchy.tupleDecode.match_1 _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq _root_.Complexity.PrefixByLength.instDecidableEqLabel.decEq.match_1 _root_.Complexity.PrefixByLength.instFintypeLabel.match_3 _root_.Complexity.PrefixByLength.instFintypeLabel.match_5 _root_.Complexity.PrefixByLength.take _root_.Complexity.StateLoop.BlockMapLoop.acc _root_.Complexity.StateLoop.BlockMapLoop.out _root_.Complexity.StateLoop.BlockMapLoop.rounds _root_.Complexity.StateLoop.BlockMapLoop.start _root_.Complexity.StateLoop.BlockMapLoop.step _root_.Complexity.StateLoop.EmitLoop.out _root_.Complexity.StateLoop.EmitLoop.start _root_.Complexity.StateLoop.EmitLoop.step _root_.Complexity.StateLoop.EqLoop.flag _root_.Complexity.StateLoop.EqLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.EqLoop.out _root_.Complexity.StateLoop.EqLoop.step _root_.Complexity.StateLoop.IterLoop.acc _root_.Complexity.StateLoop.IterLoop.out _root_.Complexity.StateLoop.IterLoop.start _root_.Complexity.StateLoop.IterLoop.step _root_.Complexity.StateLoop.MajLoop.acc _root_.Complexity.StateLoop.MajLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.MajLoop.out _root_.Complexity.StateLoop.MajLoop.start _root_.Complexity.StateLoop.MajLoop.step _root_.Complexity.StateLoop.XorLoop.acc _root_.Complexity.StateLoop.XorLoop.orbit_eq.match_1_1 _root_.Complexity.StateLoop.XorLoop.out _root_.Complexity.StateLoop.XorLoop.rounds _root_.Complexity.StateLoop.XorLoop.start _root_.Complexity.StateLoop.XorLoop.step _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.StateLoop.length_flatMap_range_le.match_1_1 _root_.Complexity.StateLoop.orbit _root_.Complexity.StateLoop.orbit.match_1 _root_.Complexity.TimeConstructible _root_.Complexity.blockAt _root_.Complexity.blockDone _root_.Complexity.coNP _root_.Complexity.guardedStep _root_.Complexity.instDecidableEqPolyExpr.decEq _root_.Complexity.instDecidableEqPolyExpr.decEq.match_1 _root_.Complexity.instReprPolyExpr.repr _root_.Complexity.instReprPolyExpr.repr.match_1 _root_.Complexity.isNilB _root_.Complexity.pairFstD _root_.Complexity.pairMapSnd _root_.Complexity.pairMapSnd.match_1 _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.Complexity.polyTimeComputable_unary.match_1_1 _root_.Complexity.sliceDropAt _root_.Complexity.sliceTakeAt _root_.Complexity.transduce _root_.Complexity.transduce.match_1 _root_.Complexity.transducerTM _root_.Complexity.transducerTr _root_.Complexity.transducerTr.match_1 _root_.Complexity.xorD _root_.Language.InLayeredPPoly _root_.Language.InLayeredSIZE _root_.Language.InPPoly _root_.Language.InSIZE _root_.Language.allOnes _root_.Light.AbsLe _root_.Light.sumLists _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.padded _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Collection.EvalSampled _root_.TCSlib.Cryptography.Collection.HardCore _root_.TCSlib.Cryptography.Collection.HardCore.evaluator.match_1_1 _root_.TCSlib.Cryptography.Collection.OneWay.exists_strongOneWay.match_1_1 _root_.TCSlib.Cryptography.Collection.OutLenBound _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.glBit _root_.TCSlib.Cryptography.Collection.glPad _root_.TCSlib.Cryptography.Collection.glPad.match_1 _root_.TCSlib.Cryptography.Collection.glPad.match_3 _root_.TCSlib.Cryptography.Collection.glPadSampleFun _root_.TCSlib.Cryptography.Collection.glPad_domEquiv _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.Collection.owfCoinsEquiv _root_.TCSlib.Cryptography.Collection.owfFamily _root_.TCSlib.Cryptography.Collection.owfRaw _root_.TCSlib.Cryptography.Collection.sample_eq_encD.match_1_1 _root_.TCSlib.Cryptography.Collection.trap _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDin_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acDout_eval.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acEnc _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHandler _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acHyb _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acSeedTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acStLen _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acState _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.acTapes _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.castImpl_adaptiveIndImpl.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.expect_tapeImpl.match_1_4 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.extTape _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl.match_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.hybImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.msgOf _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.simulate_tapeImpl_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.tapeImpl _root_.TCSlib.Cryptography.Composability.Attack.ofNat _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun_some_congr.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.length_of_firstQ_eq_some.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.recAdvIn _root_.TCSlib.Cryptography.Composability.ChallengeSim.recDin _root_.TCSlib.Cryptography.Composability.ChallengeSim.recDin.match_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.recDout _root_.TCSlib.Cryptography.Composability.ChallengeSim.recHandler _root_.TCSlib.Cryptography.Composability.ChallengeSim.recOut _root_.TCSlib.Cryptography.Composability.ChallengeSim.recRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.simulate_recHandler_init.match_1_1 _root_.TCSlib.Cryptography.Composability.ChallengeSim.simulate_recHandler_recorded.match_1_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.AdaptiveINDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.NMSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.adaptiveIndImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmDecrypt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nmOutput _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.nthCt _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.ofPadded _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_1 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl.match_3 _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.NMCCA2.ansRead _root_.TCSlib.Cryptography.Composability.NMCCA2.cntRead _root_.TCSlib.Cryptography.Composability.NMCCA2.decBlock _root_.TCSlib.Cryptography.Composability.NMCCA2.decHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encCt _root_.TCSlib.Cryptography.Composability.NMCCA2.encHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.encTape _root_.TCSlib.Cryptography.Composability.NMCCA2.finA _root_.TCSlib.Cryptography.Composability.NMCCA2.finL _root_.TCSlib.Cryptography.Composability.NMCCA2.finU _root_.TCSlib.Cryptography.Composability.NMCCA2.finW _root_.TCSlib.Cryptography.Composability.NMCCA2.finZ _root_.TCSlib.Cryptography.Composability.NMCCA2.fwdHandler _root_.TCSlib.Cryptography.Composability.NMCCA2.guessBit _root_.TCSlib.Cryptography.Composability.NMCCA2.guessDist _root_.TCSlib.Cryptography.Composability.NMCCA2.indImpl_eq_of_msgLen_eq_zero.match_1_1 _root_.TCSlib.Cryptography.Composability.NMCCA2.logEmit _root_.TCSlib.Cryptography.Composability.isPadded _root_.TCSlib.Cryptography.Composability.padCt _root_.TCSlib.Cryptography.Composability.padDecFun _root_.TCSlib.Cryptography.Composability.padEncFun _root_.TCSlib.Cryptography.Distinguishes _root_.TCSlib.Cryptography.Ensemble.DistinguishesWith _root_.TCSlib.Cryptography.Ensemble.Indist _root_.TCSlib.Cryptography.Ensemble.IndistLit _root_.TCSlib.Cryptography.Ensemble.NextBitUnpredictable _root_.TCSlib.Cryptography.Ensemble.Pseudorandom _root_.TCSlib.Cryptography.Ensemble.Samplable _root_.TCSlib.Cryptography.Ensemble.copies _root_.TCSlib.Cryptography.Ensemble.push _root_.TCSlib.Cryptography.Ensemble.uniform _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.emit _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.loopOut _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₁ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₂ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₃ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₄ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₅ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.p₆ _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.st _root_.TCSlib.Cryptography.EnsembleLemmas.CopiesLoop.step _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.coinsEquiv _root_.TCSlib.Cryptography.EnsembleLemmas.consSplit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesInit _root_.TCSlib.Cryptography.EnsembleLemmas.copiesSampler _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.EnsembleLemmas.statClose_copies.match_1_1 _root_.TCSlib.Cryptography.EnsembleLemmas.swapAux _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.LengthRegular _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.glBit _root_.TCSlib.Cryptography.FunFamily.glInverter _root_.TCSlib.Cryptography.FunFamily.glPad _root_.TCSlib.Cryptography.FunFamily.glPad_inEquiv _root_.TCSlib.Cryptography.FunFamily.glPad_outEquiv _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.ofString _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.FunFamily.strOutLen _root_.TCSlib.Cryptography.FunFamily.toCollection _root_.TCSlib.Cryptography.FunFamily.toCollection_domEquiv _root_.TCSlib.Cryptography.GGMRed.IsQ _root_.TCSlib.Cryptography.GGMRed.acc _root_.TCSlib.Cryptography.GGMRed.advD _root_.TCSlib.Cryptography.GGMRed.advPoly _root_.TCSlib.Cryptography.GGMRed.adviceOf _root_.TCSlib.Cryptography.GGMRed.ans _root_.TCSlib.Cryptography.GGMRed.ansMap _root_.TCSlib.Cryptography.GGMRed.bound _root_.TCSlib.Cryptography.GGMRed.buildTreeQ _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_1 _root_.TCSlib.Cryptography.GGMRed.buildTreeQ.match_3 _root_.TCSlib.Cryptography.GGMRed.chal _root_.TCSlib.Cryptography.GGMRed.cnt _root_.TCSlib.Cryptography.GGMRed.cnt' _root_.TCSlib.Cryptography.GGMRed.coinPoly _root_.TCSlib.Cryptography.GGMRed.coinStr _root_.TCSlib.Cryptography.GGMRed.coinsAll _root_.TCSlib.Cryptography.GGMRed.coinsD _root_.TCSlib.Cryptography.GGMRed.coinsRest _root_.TCSlib.Cryptography.GGMRed.concrete _root_.TCSlib.Cryptography.GGMRed.concrete_iterate.match_1_1 _root_.TCSlib.Cryptography.GGMRed.encState _root_.TCSlib.Cryptography.GGMRed.eqJ _root_.TCSlib.Cryptography.GGMRed.firstRound _root_.TCSlib.Cryptography.GGMRed.fresh _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine _root_.TCSlib.Cryptography.GGMRed.ggmRedMachine_coinsEquiv _root_.TCSlib.Cryptography.GGMRed.hist _root_.TCSlib.Cryptography.GGMRed.hist' _root_.TCSlib.Cryptography.GGMRed.histEnc _root_.TCSlib.Cryptography.GGMRed.inS _root_.TCSlib.Cryptography.GGMRed.inX _root_.TCSlib.Cryptography.GGMRed.isQ _root_.TCSlib.Cryptography.GGMRed.lab _root_.TCSlib.Cryptography.GGMRed.look _root_.TCSlib.Cryptography.GGMRed.lookAcc _root_.TCSlib.Cryptography.GGMRed.lookAcc_tblEnc.match_1 _root_.TCSlib.Cryptography.GGMRed.lookOut _root_.TCSlib.Cryptography.GGMRed.lookStep _root_.TCSlib.Cryptography.GGMRed.lookStep_iterate_tblEnc.match_1_1 _root_.TCSlib.Cryptography.GGMRed.lookup _root_.TCSlib.Cryptography.GGMRed.ltJ _root_.TCSlib.Cryptography.GGMRed.move _root_.TCSlib.Cryptography.GGMRed.mul1 _root_.TCSlib.Cryptography.GGMRed.mul2 _root_.TCSlib.Cryptography.GGMRed.nextQ _root_.TCSlib.Cryptography.GGMRed.notFound _root_.TCSlib.Cryptography.GGMRed.orbit_eq_encState.match_1_1 _root_.TCSlib.Cryptography.GGMRed.out _root_.TCSlib.Cryptography.GGMRed.pairs _root_.TCSlib.Cryptography.GGMRed.paramU _root_.TCSlib.Cryptography.GGMRed.pfx _root_.TCSlib.Cryptography.GGMRed.prefMap _root_.TCSlib.Cryptography.GGMRed.pureAt _root_.TCSlib.Cryptography.GGMRed.pureStep _root_.TCSlib.Cryptography.GGMRed.pureStep.match_1 _root_.TCSlib.Cryptography.GGMRed.query _root_.TCSlib.Cryptography.GGMRed.queryOf _root_.TCSlib.Cryptography.GGMRed.queryOf.match_1 _root_.TCSlib.Cryptography.GGMRed.rawFun _root_.TCSlib.Cryptography.GGMRed.rawInput _root_.TCSlib.Cryptography.GGMRed.rnd _root_.TCSlib.Cryptography.GGMRed.seeds _root_.TCSlib.Cryptography.GGMRed.start _root_.TCSlib.Cryptography.GGMRed.stateLoopFun _root_.TCSlib.Cryptography.GGMRed.stateLoopFun.match_1 _root_.TCSlib.Cryptography.GGMRed.step _root_.TCSlib.Cryptography.GGMRed.stream _root_.TCSlib.Cryptography.GGMRed.tbl _root_.TCSlib.Cryptography.GGMRed.tbl' _root_.TCSlib.Cryptography.GGMRed.tblEnc _root_.TCSlib.Cryptography.GGMRed.tblOf _root_.TCSlib.Cryptography.GGMRed.tblOf.match_1 _root_.TCSlib.Cryptography.GGMRed.un2 _root_.TCSlib.Cryptography.GGMRed.unI _root_.TCSlib.Cryptography.GGMRed.unJ _root_.TCSlib.Cryptography.GGMRed.unQ _root_.TCSlib.Cryptography.GGMRed.valStr _root_.TCSlib.Cryptography.GGMRed.verdictOf _root_.TCSlib.Cryptography.GGMRed.vstr _root_.TCSlib.Cryptography.GLLoop.bound _root_.TCSlib.Cryptography.GLLoop.entry _root_.TCSlib.Cryptography.GLLoop.fixed _root_.TCSlib.Cryptography.GLLoop.fx _root_.TCSlib.Cryptography.GLLoop.glEntry _root_.TCSlib.Cryptography.GLLoop.glEntryFn _root_.TCSlib.Cryptography.GLLoop.glTable _root_.TCSlib.Cryptography.GLLoop.input _root_.TCSlib.Cryptography.GLLoop.out _root_.TCSlib.Cryptography.GLLoop.pY _root_.TCSlib.Cryptography.GLLoop.pb _root_.TCSlib.Cryptography.GLLoop.pcs _root_.TCSlib.Cryptography.GLLoop.ps _root_.TCSlib.Cryptography.GLLoop.ptbl _root_.TCSlib.Cryptography.GLLoop.pu _root_.TCSlib.Cryptography.GLLoop.puk _root_.TCSlib.Cryptography.GLLoop.pum _root_.TCSlib.Cryptography.GLLoop.pur _root_.TCSlib.Cryptography.GLLoop.pvotes _root_.TCSlib.Cryptography.GLLoop.pα _root_.TCSlib.Cryptography.GLLoop.start _root_.TCSlib.Cryptography.GLLoop.step _root_.TCSlib.Cryptography.GLLoop.vote _root_.TCSlib.Cryptography.GLLoop.wfInput _root_.TCSlib.Cryptography.GLLoop.wfVote _root_.TCSlib.Cryptography.GLRaw.adv _root_.TCSlib.Cryptography.GLRaw.cb _root_.TCSlib.Cryptography.GLRaw.cs₁ _root_.TCSlib.Cryptography.GLRaw.cs₂ _root_.TCSlib.Cryptography.GLRaw.r₁ _root_.TCSlib.Cryptography.GLRaw.tbl _root_.TCSlib.Cryptography.GLRaw.uM _root_.TCSlib.Cryptography.GLRaw.uk _root_.TCSlib.Cryptography.GLRaw.ukm _root_.TCSlib.Cryptography.GLRaw.um _root_.TCSlib.Cryptography.GLRaw.ur _root_.TCSlib.Cryptography.GLRaw.α _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.Bridge.treeImpl _root_.TCSlib.Cryptography.Games.EffFill.IInv _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom _root_.TCSlib.Cryptography.Games.EffFill.ReplaysFrom.match_1 _root_.TCSlib.Cryptography.Games.EffFill.RunsTo _root_.TCSlib.Cryptography.Games.EffFill.actAcc _root_.TCSlib.Cryptography.Games.EffFill.actLoop _root_.TCSlib.Cryptography.Games.EffFill.actStep _root_.TCSlib.Cryptography.Games.EffFill.advNext _root_.TCSlib.Cryptography.Games.EffFill.bridgePost _root_.TCSlib.Cryptography.Games.EffFill.bridgePre _root_.TCSlib.Cryptography.Games.EffFill.canonFun _root_.TCSlib.Cryptography.Games.EffFill.canonQ _root_.TCSlib.Cryptography.Games.EffFill.canonR _root_.TCSlib.Cryptography.Games.EffFill.canonWord _root_.TCSlib.Cryptography.Games.EffFill.entryPoly _root_.TCSlib.Cryptography.Games.EffFill.eval_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.fixLen _root_.TCSlib.Cryptography.Games.EffFill.gB _root_.TCSlib.Cryptography.Games.EffFill.gC _root_.TCSlib.Cryptography.Games.EffFill.gCur _root_.TCSlib.Cryptography.Games.EffFill.gLc _root_.TCSlib.Cryptography.Games.EffFill.gLin _root_.TCSlib.Cryptography.Games.EffFill.gO _root_.TCSlib.Cryptography.Games.EffFill.gPh _root_.TCSlib.Cryptography.Games.EffFill.gS _root_.TCSlib.Cryptography.Games.EffFill.hAct _root_.TCSlib.Cryptography.Games.EffFill.hBound _root_.TCSlib.Cryptography.Games.EffFill.hCtx _root_.TCSlib.Cryptography.Games.EffFill.hMove _root_.TCSlib.Cryptography.Games.EffFill.hNext _root_.TCSlib.Cryptography.Games.EffFill.hRaw _root_.TCSlib.Cryptography.Games.EffFill.hRes _root_.TCSlib.Cryptography.Games.EffFill.hRounds _root_.TCSlib.Cryptography.Games.EffFill.hStart _root_.TCSlib.Cryptography.Games.EffFill.hState _root_.TCSlib.Cryptography.Games.EffFill.iAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvAct _root_.TCSlib.Cryptography.Games.EffFill.iAdvMove _root_.TCSlib.Cryptography.Games.EffFill.iAnsLen _root_.TCSlib.Cryptography.Games.EffFill.iAsk _root_.TCSlib.Cryptography.Games.EffFill.iBound _root_.TCSlib.Cryptography.Games.EffFill.iCall _root_.TCSlib.Cryptography.Games.EffFill.iCallAct _root_.TCSlib.Cryptography.Games.EffFill.iCallEnd _root_.TCSlib.Cryptography.Games.EffFill.iCallMove _root_.TCSlib.Cryptography.Games.EffFill.iCallNext _root_.TCSlib.Cryptography.Games.EffFill.iCtx _root_.TCSlib.Cryptography.Games.EffFill.iCurBound _root_.TCSlib.Cryptography.Games.EffFill.iFinAct _root_.TCSlib.Cryptography.Games.EffFill.iFinMove _root_.TCSlib.Cryptography.Games.EffFill.iFinNext _root_.TCSlib.Cryptography.Games.EffFill.iFinish _root_.TCSlib.Cryptography.Games.EffFill.iFixBound _root_.TCSlib.Cryptography.Games.EffFill.iImpl _root_.TCSlib.Cryptography.Games.EffFill.iNext _root_.TCSlib.Cryptography.Games.EffFill.iOuter _root_.TCSlib.Cryptography.Games.EffFill.iRaw _root_.TCSlib.Cryptography.Games.EffFill.iRounds _root_.TCSlib.Cryptography.Games.EffFill.iSt _root_.TCSlib.Cryptography.Games.EffFill.iStart _root_.TCSlib.Cryptography.Games.EffFill.iTree _root_.TCSlib.Cryptography.Games.EffFill.iX _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_encodeLog_le_append.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.length_le_length_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.logHist _root_.TCSlib.Cryptography.Games.EffFill.relabel _root_.TCSlib.Cryptography.Games.EffFill.relabelEmit _root_.TCSlib.Cryptography.Games.EffFill.relabelN _root_.TCSlib.Cryptography.Games.EffFill.relabelN_encodeHist.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen _root_.TCSlib.Cryptography.Games.EffFill.selLen.match_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_eq.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_le_sumPoly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_of_ge.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.selLen_poly.match_1_1 _root_.TCSlib.Cryptography.Games.EffFill.sumPoly _root_.TCSlib.Cryptography.Games.EffFill.sumPoly.match_1 _root_.TCSlib.Cryptography.Games.InteractiveHandler.advInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.call _root_.TCSlib.Cryptography.Games.InteractiveHandler.finInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.finish _root_.TCSlib.Cryptography.Games.InteractiveHandler.impl _root_.TCSlib.Cryptography.Games.InteractiveHandler.input _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.bind.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.call _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.OracleComp.evalFn.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft _root_.TCSlib.Cryptography.Games.OracleComp.liftLeft.match_1 _root_.TCSlib.Cryptography.Games.OracleComp.liftRight _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.answer.match_1 _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.dist _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.expect.match_1 _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.ProbComp.sampleFin _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.QueryImpl.passthrough _root_.TCSlib.Cryptography.Games.QueryImpl.sum _root_.TCSlib.Cryptography.Games.QueryImpl.sum.match_1 _root_.TCSlib.Cryptography.Games.QueryImpl.withLog _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.buildComp.match_1 _root_.TCSlib.Cryptography.Games.buildComp.match_3 _root_.TCSlib.Cryptography.Games.buildComp_costBoundedBy.match_1_1 _root_.TCSlib.Cryptography.Games.buildComp_singleCodec.match_1_1 _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.decodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_3 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_5 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_7 _root_.TCSlib.Cryptography.Games.decodeBitMove.match_9 _root_.TCSlib.Cryptography.Games.decodeIdx _root_.TCSlib.Cryptography.Games.encodeBitMove _root_.TCSlib.Cryptography.Games.encodeBitMove.match_1 _root_.TCSlib.Cryptography.Games.guessAdv _root_.TCSlib.Cryptography.Games.guessGame _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.simulate.match_1 _root_.TCSlib.Cryptography.Games.singleCodec _root_.TCSlib.Cryptography.Games.singleCodec.match_1 _root_.TCSlib.Cryptography.Games.toHist _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.HardCore _root_.TCSlib.Cryptography.HardcoreBit.PairwiseIndep _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.glBit _root_.TCSlib.Cryptography.HardcoreBit.glInverter _root_.TCSlib.Cryptography.HardcoreBit.glPad _root_.TCSlib.Cryptography.HardcoreBit.guessCoinsCongr _root_.TCSlib.Cryptography.HardcoreBit.guessInverter _root_.TCSlib.Cryptography.HardcoreBit.guessRecover _root_.TCSlib.Cryptography.HardcoreBit.idealRecover _root_.TCSlib.Cryptography.HardcoreBit.ind _root_.TCSlib.Cryptography.HardcoreBit.ip _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.HardcoreBit.majorityInverter _root_.TCSlib.Cryptography.HardcoreBit.majorityRecover _root_.TCSlib.Cryptography.HardcoreBit.pairwiseUniform_subsetSum.match_1_2 _root_.TCSlib.Cryptography.HardcoreBit.perfectInverter _root_.TCSlib.Cryptography.HardcoreBit.perfectRecover _root_.TCSlib.Cryptography.HardcoreBit.secProb _root_.TCSlib.Cryptography.HardcoreBit.subsetSum _root_.TCSlib.Cryptography.HardcoreBit.subsetSumHom _root_.TCSlib.Cryptography.HardcoreBit.trialBit _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.Noticeable _root_.TCSlib.Cryptography.OneWay.PosLoop.acc _root_.TCSlib.Cryptography.OneWay.PosLoop.rest _root_.TCSlib.Cryptography.OneWay.PosLoop.step _root_.TCSlib.Cryptography.OneWay.PosLoop.trial _root_.TCSlib.Cryptography.OneWay.PosLoop.uM _root_.TCSlib.Cryptography.OneWay.PosLoop.ukk _root_.TCSlib.Cryptography.OneWay.PosLoop.unum _root_.TCSlib.Cryptography.OneWay.ProdEval.cnt _root_.TCSlib.Cryptography.OneWay.ProdEval.emit _root_.TCSlib.Cryptography.OneWay.ProdEval.rest _root_.TCSlib.Cryptography.OneWay.ProdEval.start _root_.TCSlib.Cryptography.OneWay.ProdEval.step _root_.TCSlib.Cryptography.OneWay.ProdEval.u _root_.TCSlib.Cryptography.OneWay.UnaryOf.Inv _root_.TCSlib.Cryptography.OneWay.UnaryOf.acc _root_.TCSlib.Cryptography.OneWay.UnaryOf.capped _root_.TCSlib.Cryptography.OneWay.UnaryOf.dbl _root_.TCSlib.Cryptography.OneWay.UnaryOf.pad _root_.TCSlib.Cryptography.OneWay.UnaryOf.rest _root_.TCSlib.Cryptography.OneWay.UnaryOf.start _root_.TCSlib.Cryptography.OneWay.UnaryOf.step _root_.TCSlib.Cryptography.OneWay.YaoMachine.acc _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.alpha1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.g _root_.TCSlib.Cryptography.OneWay.YaoMachine.ipos _root_.TCSlib.Cryptography.OneWay.YaoMachine.nkk _root_.TCSlib.Cryptography.OneWay.YaoMachine.off _root_.TCSlib.Cryptography.OneWay.YaoMachine.offIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.planted _root_.TCSlib.Cryptography.OneWay.YaoMachine.posBits _root_.TCSlib.Cryptography.OneWay.YaoMachine.rc _root_.TCSlib.Cryptography.OneWay.YaoMachine.rcoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.sampleAll _root_.TCSlib.Cryptography.OneWay.YaoMachine.test _root_.TCSlib.Cryptography.OneWay.YaoMachine.uIn _root_.TCSlib.Cryptography.OneWay.YaoMachine.uM _root_.TCSlib.Cryptography.OneWay.YaoMachine.uOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ukk _root_.TCSlib.Cryptography.OneWay.YaoMachine.xs _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw' _root_.TCSlib.Cryptography.OneWay.YaoMachine.yaoRaw.match_1 _root_.TCSlib.Cryptography.OneWay.YaoMachine.ys _root_.TCSlib.Cryptography.OneWay.YaoMachine.zOut _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρPEquiv _root_.TCSlib.Cryptography.OneWay.bitListToNat _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.pad _root_.TCSlib.Cryptography.OneWay.padInverter _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.pbOf _root_.TCSlib.Cryptography.OneWay.posOf _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundEquiv _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.tableInverter _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoBad _root_.TCSlib.Cryptography.OneWay.yaoInverter _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.OneWay.yaoTryProb _root_.TCSlib.Cryptography.OneWayPermutation _root_.TCSlib.Cryptography.OracleAdversary.BoundedBy _root_.TCSlib.Cryptography.OracleEnsemble.Indist _root_.TCSlib.Cryptography.OracleEnsemble.keyed _root_.TCSlib.Cryptography.OracleEnsemble.random _root_.TCSlib.Cryptography.PRG.Easy _root_.TCSlib.Cryptography.PRG.Secure _root_.TCSlib.Cryptography.PRG.doubling _root_.TCSlib.Cryptography.PRG.ensemble _root_.TCSlib.Cryptography.PRG.expand _root_.TCSlib.Cryptography.PRG.oneBit _root_.TCSlib.Cryptography.PRG.truncate _root_.TCSlib.Cryptography.PermCollection.OneWay _root_.TCSlib.Cryptography.PermCollection.glPad _root_.TCSlib.Cryptography.PermCollection.glPad_domEquiv _root_.TCSlib.Cryptography.PermFamily.HardCore _root_.TCSlib.Cryptography.PermFamily.glHalf _root_.TCSlib.Cryptography.PermFamily.glHalfFun _root_.TCSlib.Cryptography.PermFamily.glHalfInv _root_.TCSlib.Cryptography.PermFamily.glPad_inEquiv _root_.TCSlib.Cryptography.PermFamily.glPad_outEquiv _root_.TCSlib.Cryptography.PermFamily.iterPRG _root_.TCSlib.Cryptography.PermFamily.toFunFamily _root_.TCSlib.Cryptography.PermFamily.toFunFamily_codEquiv _root_.TCSlib.Cryptography.PermFamily.toFunFamily_domEquiv _root_.TCSlib.Cryptography.PrivateKeyScheme.Deterministic _root_.TCSlib.Cryptography.PrivateKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.SingleMessageSecure _root_.TCSlib.Cryptography.PrivateKeyScheme.encDist _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList.match_1 _root_.TCSlib.Cryptography.PrivateKeyScheme.firstTwoEqFun _root_.TCSlib.Cryptography.PrivateKeyScheme.multiEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.MultiMessageSecure _root_.TCSlib.Cryptography.PublicKeyScheme.Secure _root_.TCSlib.Cryptography.PublicKeyScheme.padded _root_.TCSlib.Cryptography.PublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.PublicKeyScheme.pkMultiEncDist _root_.TCSlib.Cryptography.QueryTree.BoundedBy _root_.TCSlib.Cryptography.QueryTree.BoundedBy.match_1 _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.QueryTree.eval.match_1 _root_.TCSlib.Cryptography.QueryTree.evalLazy _root_.TCSlib.Cryptography.QueryTree.evalLazy.match_1 _root_.TCSlib.Cryptography.QueryTree.induct _root_.TCSlib.Cryptography.QueryTree.induct.match_1 _root_.TCSlib.Cryptography.QueryTree.noteQuery _root_.TCSlib.Cryptography.QueryTree.simulate _root_.TCSlib.Cryptography.SelXor.bound _root_.TCSlib.Cryptography.SelXor.input _root_.TCSlib.Cryptography.SelXor.out _root_.TCSlib.Cryptography.SelXor.partialSum _root_.TCSlib.Cryptography.SelXor.partialSum.match_1 _root_.TCSlib.Cryptography.SelXor.start _root_.TCSlib.Cryptography.SelXor.step _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.TrapdoorCollection.OneWay _root_.TCSlib.Cryptography.TrapdoorCollection.glPad _root_.TCSlib.Cryptography.TrapdoorCollection.glPad_domEquiv _root_.TCSlib.Cryptography.TrapdoorCollection.toCollection_domEquiv _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.betaOf _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.blockEmit _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockList _root_.TCSlib.Cryptography.blockList.match_1 _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.blockStep _root_.TCSlib.Cryptography.blocksEquiv _root_.TCSlib.Cryptography.blocksEquivX _root_.TCSlib.Cryptography.blocksStr _root_.TCSlib.Cryptography.buildTree _root_.TCSlib.Cryptography.buildTree.match_1 _root_.TCSlib.Cryptography.buildTree.match_3 _root_.TCSlib.Cryptography.buildTree_boundedBy.match_1_1 _root_.TCSlib.Cryptography.challengeStream _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.collPre _root_.TCSlib.Cryptography.completePrefix _root_.TCSlib.Cryptography.concatPre _root_.TCSlib.Cryptography.copies _root_.TCSlib.Cryptography.decListEmit _root_.TCSlib.Cryptography.decListFun _root_.TCSlib.Cryptography.decListStep _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.decodeOracleMove _root_.TCSlib.Cryptography.decodeOracleMove.match_1 _root_.TCSlib.Cryptography.decodeOracleMove.match_3 _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.doublingEnsemble _root_.TCSlib.Cryptography.encodeHist _root_.TCSlib.Cryptography.exists_owp_hardCore.match_1_1 _root_.TCSlib.Cryptography.exists_prf_of_exists_prg.match_1_1 _root_.TCSlib.Cryptography.exists_securePRG_of_owp.match_1_1 _root_.TCSlib.Cryptography.expandRed _root_.TCSlib.Cryptography.expandRedMachine _root_.TCSlib.Cryptography.expandRedPre _root_.TCSlib.Cryptography.extendStream _root_.TCSlib.Cryptography.finCastEquiv _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.ggm _root_.TCSlib.Cryptography.ggmBits _root_.TCSlib.Cryptography.ggmBitsDist _root_.TCSlib.Cryptography.ggmDist _root_.TCSlib.Cryptography.ggmEval _root_.TCSlib.Cryptography.ggmFrom_eq_walk.match_1_1 _root_.TCSlib.Cryptography.ggmPRF _root_.TCSlib.Cryptography.ggmStep _root_.TCSlib.Cryptography.ggmStep_iterate.match_1_1 _root_.TCSlib.Cryptography.glAdvPoly _root_.TCSlib.Cryptography.glAdvice _root_.TCSlib.Cryptography.glBlocks _root_.TCSlib.Cryptography.glCoins _root_.TCSlib.Cryptography.glCoinsEquiv _root_.TCSlib.Cryptography.glCollMachine _root_.TCSlib.Cryptography.glCollPost _root_.TCSlib.Cryptography.glCollPre _root_.TCSlib.Cryptography.glFamMachine _root_.TCSlib.Cryptography.glFamPost _root_.TCSlib.Cryptography.glFamPre _root_.TCSlib.Cryptography.glHalfBit _root_.TCSlib.Cryptography.glHalfOddInv _root_.TCSlib.Cryptography.glHalfOddPred _root_.TCSlib.Cryptography.glK _root_.TCSlib.Cryptography.glKBound _root_.TCSlib.Cryptography.glKc _root_.TCSlib.Cryptography.glKcBound _root_.TCSlib.Cryptography.glMachine _root_.TCSlib.Cryptography.glMachine_coinsEquiv _root_.TCSlib.Cryptography.glMajFun _root_.TCSlib.Cryptography.glPadCollInvMachine _root_.TCSlib.Cryptography.glPadCollPost _root_.TCSlib.Cryptography.glPadCollPre _root_.TCSlib.Cryptography.glPadDecode _root_.TCSlib.Cryptography.glPadDecode.match_1 _root_.TCSlib.Cryptography.glPadDecode.match_3 _root_.TCSlib.Cryptography.glPadInvFun _root_.TCSlib.Cryptography.glPadInvMachine _root_.TCSlib.Cryptography.glPadInvPost _root_.TCSlib.Cryptography.glPredictorOf _root_.TCSlib.Cryptography.glRawFun _root_.TCSlib.Cryptography.glVotesFun _root_.TCSlib.Cryptography.hybridAdv _root_.TCSlib.Cryptography.hybridCoins _root_.TCSlib.Cryptography.hybridOracle _root_.TCSlib.Cryptography.hybridPlant _root_.TCSlib.Cryptography.hybridPre _root_.TCSlib.Cryptography.hybridProb _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.ipFun _root_.TCSlib.Cryptography.lazyDist _root_.TCSlib.Cryptography.length_flatten_ofFn.match_1_1 _root_.TCSlib.Cryptography.levelAdv _root_.TCSlib.Cryptography.mixDist _root_.TCSlib.Cryptography.mixEnsemble _root_.TCSlib.Cryptography.multiDist _root_.TCSlib.Cryptography.multicopyAvgRed _root_.TCSlib.Cryptography.multicopyHybrid _root_.TCSlib.Cryptography.multicopyRed _root_.TCSlib.Cryptography.nesubsetEquiv _root_.TCSlib.Cryptography.nextBitDist _root_.TCSlib.Cryptography.nextBitHybrid _root_.TCSlib.Cryptography.nextBitHybridFlip _root_.TCSlib.Cryptography.nextBitPred _root_.TCSlib.Cryptography.nextBitProb _root_.TCSlib.Cryptography.oneBitStep _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.owpBitsEquiv _root_.TCSlib.Cryptography.owpGen _root_.TCSlib.Cryptography.owpGenBits _root_.TCSlib.Cryptography.owpGenNot _root_.TCSlib.Cryptography.owpGenPRG _root_.TCSlib.Cryptography.owpGenPRG_outEquiv _root_.TCSlib.Cryptography.owpPair _root_.TCSlib.Cryptography.owpPredMachine _root_.TCSlib.Cryptography.owpPredPost _root_.TCSlib.Cryptography.owpPredPre _root_.TCSlib.Cryptography.owpPredictor _root_.TCSlib.Cryptography.owpPredictorBits _root_.TCSlib.Cryptography.owpPredictorSnoc _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.padToLen _root_.TCSlib.Cryptography.padXor _root_.TCSlib.Cryptography.pairSel _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.prefixAt _root_.TCSlib.Cryptography.prefixOf _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prgAdv _root_.TCSlib.Cryptography.prgExt _root_.TCSlib.Cryptography.prgExtAvgRed _root_.TCSlib.Cryptography.prgExtBits _root_.TCSlib.Cryptography.prgExtBitsRed _root_.TCSlib.Cryptography.prgExtRed _root_.TCSlib.Cryptography.prgHybrid _root_.TCSlib.Cryptography.prgIterEmit _root_.TCSlib.Cryptography.prgIterFun _root_.TCSlib.Cryptography.prgIterStep _root_.TCSlib.Cryptography.prgPadFun _root_.TCSlib.Cryptography.prgScheme _root_.TCSlib.Cryptography.prgScheme_encCoinsEquiv _root_.TCSlib.Cryptography.prgScheme_genCoinsEquiv _root_.TCSlib.Cryptography.prgStep _root_.TCSlib.Cryptography.pushSampler _root_.TCSlib.Cryptography.randomFunction _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.selHalf _root_.TCSlib.Cryptography.selXorFun _root_.TCSlib.Cryptography.singleDist _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.splitHalves _root_.TCSlib.Cryptography.splitPair _root_.TCSlib.Cryptography.subHybridProb _root_.TCSlib.Cryptography.subHybridStream _root_.TCSlib.Cryptography.sunglassRed _root_.TCSlib.Cryptography.tableDist _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.unaryHalf _root_.TCSlib.Cryptography.unaryMulFun _root_.TCSlib.Cryptography.unaryMulFun.match_1 _root_.TCSlib.Cryptography.uniformFromBits _root_.TCSlib.Cryptography.uprob _root_.TCSlib.Cryptography.walk _root_.TCSlib.Cryptography.yaoBlocks _root_.TCSlib.Cryptography.yaoRounds _root_.TCSlib.InformationTheory.FinDist.HasMinEntropy _root_.TCSlib.InformationTheory.FinDist.collision _root_.TCSlib.InformationTheory.FinDist.map _root_.TCSlib.InformationTheory.FinDist.probTrue _root_.TCSlib.InformationTheory.FinDist.prod _root_.TCSlib.InformationTheory.FinDist.uniform _root_.TCSlib.InformationTheory.statDist _root_.Turing.Action.apply _root_.Turing.Action.apply.match_1 _root_.Turing.Action.mapState _root_.Turing.Cfg.ext.match_1 _root_.Turing.Cfg.init _root_.Turing.Cfg.inputSymbol _root_.Turing.Cfg.mapState _root_.Turing.Cfg.ofWords _root_.Turing.Cfg.select _root_.Turing.Cfg.workTapeSymbols _root_.Turing.CodeTM.serialize _root_.Turing.CodeTM.toFinTM _root_.Turing.FinTM.Computes _root_.Turing.FinTM.ComputesFunInTime _root_.Turing.FinTM.ComputesFunInTimeVia _root_.Turing.FinTM.ComputesInTime _root_.Turing.FinTM.DecidesInTime _root_.Turing.FinTM.DecidesWithAdviceInTime _root_.Turing.FinTM.VirtualTag _root_.Turing.FinTM.appendBitTM _root_.Turing.FinTM.branchTM _root_.Turing.FinTM.branchTM.match_1 _root_.Turing.FinTM.bufferTape _root_.Turing.FinTM.bufferedCompTM _root_.Turing.FinTM.bufferedCompTM.match_1 _root_.Turing.FinTM.bufferedFirstCfg _root_.Turing.FinTM.bufferedScanCfg _root_.Turing.FinTM.bufferedSecondCfg _root_.Turing.FinTM.callEntry _root_.Turing.FinTM.callExit _root_.Turing.FinTM.callTM _root_.Turing.FinTM.callTM.match_1 _root_.Turing.FinTM.computesFunInTime_unaryMul.match_1 _root_.Turing.FinTM.condTM _root_.Turing.FinTM.condTM.match_1 _root_.Turing.FinTM.constTM _root_.Turing.FinTM.controlAction _root_.Turing.FinTM.emitAction _root_.Turing.FinTM.idTM _root_.Turing.FinTM.idTM.match_1 _root_.Turing.FinTM.ifEqTM _root_.Turing.FinTM.ifEqTM.match_1 _root_.Turing.FinTM.incFixedTM _root_.Turing.FinTM.incFixedTM.match_1 _root_.Turing.FinTM.incFixedTM.match_3 _root_.Turing.FinTM.indexedVisit _root_.Turing.FinTM.leftAction _root_.Turing.FinTM.leftCfg _root_.Turing.FinTM.lengthBitsTM _root_.Turing.FinTM.lengthBitsTM.match_1 _root_.Turing.FinTM.pairExtractTM _root_.Turing.FinTM.pairExtractTM.match_1 _root_.Turing.FinTM.pairExtractTM.match_3 _root_.Turing.FinTM.pairExtractTM.match_5 _root_.Turing.FinTM.pairLenCheckTM _root_.Turing.FinTM.pairValidTM _root_.Turing.FinTM.pairValidTM.match_1 _root_.Turing.FinTM.polyBitsTM _root_.Turing.FinTM.polyUnaryTM _root_.Turing.FinTM.polyUnaryTM.match_1 _root_.Turing.FinTM.prependTM _root_.Turing.FinTM.prependTM.match_1 _root_.Turing.FinTM.redirectTM _root_.Turing.FinTM.redirectTM.match_1 _root_.Turing.FinTM.redirectTM.match_3 _root_.Turing.FinTM.rewind_scan.match_1 _root_.Turing.FinTM.rightAction _root_.Turing.FinTM.rightCfg _root_.Turing.FinTM.splitSolveTM _root_.Turing.FinTM.splitSolveWithTM _root_.Turing.FinTM.stripLastTM _root_.Turing.FinTM.stripLastTM_computes.match_1 _root_.Turing.FinTM.sweepAct _root_.Turing.FinTM.sweepCfg _root_.Turing.FinTM.sweepFold _root_.Turing.FinTM.sweepFold.match_1 _root_.Turing.FinTM.sweepRevCfg _root_.Turing.FinTM.sweepTape _root_.Turing.FinTM.tapeBlocks _root_.Turing.FinTM.timedCondTM _root_.Turing.FinTM.timedCondTM.match_1 _root_.Turing.FinTM.toCodeTM _root_.Turing.FinTM.toCodeTM.match_1 _root_.Turing.FinTM.unaryTokenTM _root_.Turing.FinTM.unaryTokenTM.match_1 _root_.Turing.FinTM.virtualMove _root_.Turing.FinTM.virtualNextTag _root_.Turing.FinTM.virtualNextTag.match_1 _root_.Turing.ModuleHost.Clean _root_.Turing.ModuleHost.entry _root_.Turing.ModuleHost.hostTM _root_.Turing.ModuleHost.hostTM.match_1 _root_.Turing.MultiTapeTM.AgreeOn _root_.Turing.MultiTapeTM.ComputableInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesFunInTimeAndSpace _root_.Turing.MultiTapeTM.ComputesInTimeAndSpace _root_.Turing.MultiTapeTM.DecidableInTimeAndSpace _root_.Turing.MultiTapeTM.haltsAtStep _root_.Turing.MultiTapeTM.indicator _root_.Turing.MultiTapeTM.initCfg _root_.Turing.MultiTapeTM.outputSymbol _root_.Turing.MultiTapeTM.relabelState _root_.Turing.MultiTapeTM.runFrom _root_.Turing.MultiTapeTM.spaceUsed _root_.Turing.MultiTapeTM.spaceUsedByTape _root_.Turing.MultiTapeTM.step _root_.Turing.MultiTapeTM.step.match_1 _root_.Turing.MultiTapeTM.visitedByTapeHead _root_.Turing.PairParse.cfg _root_.Turing.PairParse.rewind_run.match_1 _root_.Turing.SafeRun _root_.Turing.UnaryTape.ones _root_.Turing.UnaryTape.wrT _root_.Turing.UnaryTape.wrT.match_1 _root_.Turing.actionBits _root_.Turing.captureAction _root_.Turing.captureAction.match_1 _root_.Turing.captureCfg _root_.Turing.dbl _root_.Turing.embedCfg _root_.Turing.embedEmitCfg _root_.Turing.embedEmitRetTM _root_.Turing.embedEmitTM _root_.Turing.embedSilentCfg _root_.Turing.embedSilentRetTM _root_.Turing.embedSilentRetTM.match_1 _root_.Turing.embedSilentTM _root_.Turing.emitAction _root_.Turing.emitCfg _root_.Turing.incFixed _root_.Turing.incFixed.match_1 _root_.Turing.instDecidableEqBodyState.decEq _root_.Turing.instDecidableEqBodyState.decEq.match_1 _root_.Turing.instInhabitedCfg.default _root_.Turing.moveInputPos _root_.Turing.optBoolBits _root_.Turing.optBoolBits.match_1 _root_.Turing.optOptBoolBits _root_.Turing.optOptBoolBits.match_1 _root_.Turing.optStateBits _root_.Turing.optStateBits.match_1 _root_.Turing.padAction _root_.Turing.pairDecode _root_.Turing.pairDecode.match_1 _root_.Turing.pairDiagTM _root_.Turing.pairDiagTM.match_1 _root_.Turing.pairDiagTM.match_3 _root_.Turing.pairEncode _root_.Turing.pairSplitAt _root_.Turing.pairSplitAt.match_1 _root_.Turing.signBits _root_.Turing.signBits.match_1 _root_.Turing.solveSplit _root_.Turing.solveSplitWith _root_.Turing.spaceUsedOfCfgs _root_.Turing.splitAtLastTrue _root_.Turing.splitAtLastTrue.match_1 _root_.Turing.stateWord _root_.Turing.unaryFin _root_.Turing.unaryTokenSplit _root_.Turing.unaryTokenSplit.match_1 _root_.Turing.visitedOfCfgs


/-- **A message sampler with a history function** [PSV07, Definition 1]: a machine `M` activated
on a `paramLen(n)`-bit parameter, whose output is the message, and a polynomial-time history
function `h`, read at `histLen(n)` bits. -/
structure MsgSampler where
  /-- The sampler, activated on the adversary's parameter. -/
  samp : NUPPT
  /-- The length of the parameter. -/
  paramLen : PolyExpr
  /-- The history function `h`. -/
  hist : List Bool → List Bool
  /-- The length at which `h(m)` is read. -/
  histLen : PolyExpr
  /-- `h` is polynomial-time. -/
  hist_poly : PolyTimeComputable hist

namespace MsgSampler

variable (M : MsgSampler)

/-- The message `m = M(a)` with the sampler's coins `ρ`, read at `ℓ` bits. -/
def draw (ℓ n : ℕ) (a : Fin (M.paramLen.eval n) → Bool) (ρ : M.samp.Coins n) : Fin ℓ → Bool :=
  padFin ℓ (M.samp.runAt n (List.ofFn a) ρ)

/-- Drawing a message pads the sampler's output on parameter `a` and coins `ρ` to `ℓ` bits. -/
theorem draw_eq (ℓ n : ℕ) (a : Fin (M.paramLen.eval n) → Bool) (ρ : M.samp.Coins n) :
    M.draw ℓ n a ρ = padFin ℓ (M.samp.runAt n (List.ofFn a) ρ) := rfl

/-- The history `h(m)`, read at `histLen(n)` bits. -/
def histAt {ℓ : ℕ} (n : ℕ) (m : Fin ℓ → Bool) : Fin (M.histLen.eval n) → Bool :=
  padFin _ (M.hist (List.ofFn m))

/-- The sampled message's history is `M.hist (List.ofFn m)`, padded to `histLen(n)` bits. -/
theorem histAt_eq {ℓ : ℕ} (n : ℕ) (m : Fin ℓ → Bool) :
    M.histAt n m = padFin (M.histLen.eval n) (M.hist (List.ofFn m)) := rfl

/-- The simulator's oracle at parameter `n`: the parameter in, the history out. -/
abbrev simSpec (n : ℕ) : OracleSpec (Fin 1) :=
  bitSpec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)

/-- The simulator's oracle is `bitSpec` with parameter-length queries and history-length
answers. -/
theorem simSpec_eq (n : ℕ) :
    M.simSpec n = bitSpec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n) := rfl

end MsgSampler

namespace FixedLengthPKScheme

variable (S : FixedLengthPKScheme)

/-! ### The real experiment -/

/-- The query lengths of the real experiment's oracles `Dec` and `Challenge`. -/
def snmInLens (M : MsgSampler) (n : ℕ) : Fin 2 → ℕ
  | 0 => S.ctLen.eval n
  | 1 => M.paramLen.eval n

/-- A real-experiment decryption query has `ctLen(n)` bits. -/
theorem snmInLens_zero (M : MsgSampler) (n : ℕ) :
    S.snmInLens M n 0 = S.ctLen.eval n := rfl

/-- A real-experiment challenge query has `paramLen(n)` bits. -/
theorem snmInLens_one (M : MsgSampler) (n : ℕ) :
    S.snmInLens M n 1 = M.paramLen.eval n := rfl

/-- The answer lengths: `Dec` answers a validity flag and a message; `Challenge` the challenge
ciphertext and the history. -/
def snmOutLens (M : MsgSampler) (n : ℕ) : Fin 2 → ℕ
  | 0 => S.msgLen.eval n + 1
  | 1 => S.ctLen.eval n + M.histLen.eval n

/-- A real-experiment decryption answer has one validity bit followed by `msgLen(n)` bits. -/
theorem snmOutLens_zero (M : MsgSampler) (n : ℕ) :
    S.snmOutLens M n 0 = S.msgLen.eval n + 1 := rfl

/-- A real-experiment challenge answer has `ctLen(n) + histLen(n)` bits. -/
theorem snmOutLens_one (M : MsgSampler) (n : ℕ) :
    S.snmOutLens M n 1 = S.ctLen.eval n + M.histLen.eval n := rfl

/-- The two oracles of the real experiment at parameter `n`. -/
abbrev snmSpec (M : MsgSampler) (n : ℕ) : OracleSpec (Fin 2) :=
  bitSpec (S.snmInLens M n) (S.snmOutLens M n)

/-- The real experiment's oracle specification is `bitSpec` at its published query and
answer lengths. -/
theorem snmSpec_eq (M : MsgSampler) (n : ℕ) :
    S.snmSpec M n = bitSpec (S.snmInLens M n) (S.snmOutLens M n) := rfl

/-- The state of the real experiment's oracles: the challenge, with the parameter it was asked
on, once asked. -/
abbrev SnmState (M : MsgSampler) (n : ℕ) : Type :=
  Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (M.paramLen.eval n) → Bool))

/-- The real oracle state is an optional pair of a `ctLen(n)`-bit ciphertext and a
`paramLen(n)`-bit sampler parameter. -/
theorem SnmState_eq (M : MsgSampler) (n : ℕ) :
    S.SnmState M n =
      Option ((Fin (S.ctLen.eval n) → Bool) × (Fin (M.paramLen.eval n) → Bool)) := rfl

/-- **The oracles of the real experiment** at parameter `n`, for the keys `pk`, `sk` and the
sampler's coins `ρ`.
- `Dec` answers as in Definition 171.5: `⟨1, Dec_sk(c)⟩` when it is open (`decOpen`) and `c` is
  not the challenge, and `⊥` (all `false`) otherwise.
- `Challenge` on the parameter `a`, the first time: `m = M(a; ρ)`, `y ← Enc_pk(m)`; it answers
  `⟨y, h(m)⟩` and records `(y, a)`. Later it repeats the recorded answer. -/
noncomputable def snmImpl (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) : QueryImpl (S.snmSpec M n) (S.SnmState M n) unifSpec
  | 0, c, s =>
    if FixedLengthScheme.decOpen atk s.isSome && !decide (s.map Prod.fst = some c) then
      .pure (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))), s)
    else .pure (zeroBits _, s)
  | 1, a, s =>
    match s with
    | some (y, a₀) => .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a₀ ρ)), s)
    | none =>
      (ProbComp.sample (S.enc.Coins n)).bind fun re =>
        let y : Fin (S.ctLen.eval n) → Bool :=
          padFin _ (S.enc.runAt n (pairEncode pk (List.ofFn (M.draw (S.msgLen.eval n) n a ρ))) re)
        .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a ρ)), some (y, a))

/-- A real-experiment decryption query returns the encoded decryption exactly when the oracle
is open and the ciphertext is not the recorded challenge; otherwise it returns all-false bits. -/
theorem snmImpl_dec (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) (c : Fin (S.ctLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl atk M n pk sk ρ 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s.map Prod.fst = some c) then
        .pure (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c)))), s)
      else .pure (zeroBits (S.msgLen.eval n + 1), s) := rfl

/-- A real-experiment challenge query repeats the recorded ciphertext and history when a
challenge exists; otherwise it encrypts the sampled message and records the ciphertext and
parameter [PSV07, Definition 1]. -/
theorem snmImpl_challenge (atk : Attack) (M : MsgSampler) (n : ℕ) (pk sk : List Bool)
    (ρ : M.samp.Coins n) (a : Fin (M.paramLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl atk M n pk sk ρ 1 a s =
      match s with
      | some (y, a₀) => .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a₀ ρ)), s)
      | none =>
        (ProbComp.sample (S.enc.Coins n)).bind fun re =>
          let y : Fin (S.ctLen.eval n) → Bool :=
            padFin (S.ctLen.eval n)
              (S.enc.runAt n (pairEncode pk (List.ofFn (M.draw (S.msgLen.eval n) n a ρ))) re)
          .pure (Fin.append y (M.histAt n (M.draw (S.msgLen.eval n) n a ρ)), some (y, a)) := rfl

/-- Under CPA, `Dec` never answers. -/
theorem snmImpl_dec_cpa (M : MsgSampler) (n : ℕ) (pk sk : List Bool) (ρ : M.samp.Coins n)
    (c : Fin (S.ctLen.eval n) → Bool) (s : S.SnmState M n) :
    S.snmImpl .cpa M n pk sk ρ 0 c s = .pure (zeroBits _, s) := by
  simp [snmImpl, FixedLengthScheme.decOpen_cpa]

/-- The codec of the adversary: the two oracles, and a final output of `r` ciphertexts followed by
an `sl`-bit `σ`. -/
def snmCodec (M : MsgSampler) (n r sl : ℕ) :
    MachineCodec (S.snmSpec M n) (Fin (r * S.ctLen.eval n + sl) → Bool) :=
  bitCodec (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl)

/-- The real-experiment codec uses `decodeBitMove` with `r * ctLen(n) + sl` output bits. -/
theorem snmCodec_decodeMove (M : MsgSampler) (n r sl : ℕ) (w : List Bool) :
    (S.snmCodec M n r sl).decodeMove w =
      decodeBitMove (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) w :=
  bitCodec_decodeMove (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) w

/-- The real-experiment codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem snmCodec_encodeEntry (M : MsgSampler) (n r sl : ℕ)
    (e : Σ i, (S.snmSpec M n).dom i × (S.snmSpec M n).rng i) :
    (S.snmCodec M n r sl).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) e

/-- When its query budget expires, the real-experiment codec returns
`zeroBits (r * ctLen(n) + sl)`. -/
theorem snmCodec_timeout (M : MsgSampler) (n r sl : ℕ) :
    (S.snmCodec M n r sl).timeout = zeroBits (r * S.ctLen.eval n + sl) :=
  bitCodec_timeout (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl)

/-- The `i`-th of the `r` ciphertexts in an adversary's output. -/
def snmCt {n r sl : ℕ} (w : Fin (r * S.ctLen.eval n + sl) → Bool) (i : Fin r) :
    Fin (S.ctLen.eval n) → Bool :=
  fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j)))

/-- Real output ciphertext `i` has bit `j` at `Fin.castAdd sl (finProdFinEquiv (i, j))`. -/
theorem snmCt_eq {n r sl : ℕ} (w : Fin (r * S.ctLen.eval n + sl) → Bool) (i : Fin r) :
    S.snmCt w i = fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j))) := rfl

/-- The final `σ`: the last `sl` bits of an output. -/
def snmSigma {k sl : ℕ} (w : Fin (k + sl) → Bool) : Fin sl → Bool :=
  fun j => w (Fin.natAdd k j)

/-- The final output string's bit `j` is input bit `Fin.natAdd k j`. -/
theorem snmSigma_eq {k sl : ℕ} (w : Fin (k + sl) → Bool) :
    snmSigma w = fun j => w (Fin.natAdd k j) := rfl

/-- **The entry `d_i`** [PSV07, Definition 1]: `COPY` if `copy`, and `Dec_sk(c)` otherwise.
Encoded as a `COPY` flag followed by `Dec`'s answer (a validity flag and the message; all `false`
for `⊥`). -/
def snmEntry {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    Fin (S.msgLen.eval n + 1 + 1) → Bool :=
  if copy then Fin.cons (α := fun _ => Bool) true (zeroBits _)
  else Fin.cons (α := fun _ => Bool) false
    (FixedLengthScheme.decAnswer (decodeFin _ (S.dec (pairEncode sk (List.ofFn c)))))

/-- An entry begins with its COPY flag; a copy has an all-false payload, and every other entry
has the encoded decryption as payload [PSV07, Definition 1]. -/
theorem snmEntry_eq {n : ℕ} (sk : List Bool) (copy : Bool) (c : Fin (S.ctLen.eval n) → Bool) :
    S.snmEntry sk copy c =
      if copy then Fin.cons (α := fun _ => Bool) true (zeroBits (S.msgLen.eval n + 1))
      else Fin.cons (α := fun _ => Bool) false
        (FixedLengthScheme.decAnswer
          (decodeFin (S.msgLen.eval n) (S.dec (pairEncode sk (List.ofFn c))))) := rfl

/-- **The output `(M, m, (d₁, …, d_r), σ)`** handed to the distinguisher, with the parameter `a`
in place of `M`: the concatenation of its fixed-length parts. -/
def snmView {n pl r sl : ℕ} (a : Fin pl → Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (d : Fin r → Fin (S.msgLen.eval n + 1 + 1) → Bool) (σ : Fin sl → Bool) : List Bool :=
  List.ofFn a ++ List.ofFn m ++ (List.ofFn fun i => List.ofFn (d i)).flatten ++ List.ofFn σ

/-- The distinguisher's view concatenates the parameter, sampled message, flattened entries,
and final `σ` [PSV07, Definition 1]. -/
theorem snmView_eq {n pl r sl : ℕ} (a : Fin pl → Bool) (m : Fin (S.msgLen.eval n) → Bool)
    (d : Fin r → Fin (S.msgLen.eval n + 1 + 1) → Bool) (σ : Fin sl → Bool) :
    S.snmView a m d σ =
      List.ofFn a ++ List.ofFn m ++ (List.ofFn fun i => List.ofFn (d i)).flatten ++ List.ofFn σ :=
  rfl

/-- **The real experiment** `SIM-NME′(Π, A, n)` [PSV07, Definition 1, `ℓ = 1`] for the attack
`atk`, the sampler `M`, query budget `q`, `r` output ciphertexts and an `sl`-bit `σ`, followed
by the distinguisher `D`: sample the keys and the coins, run `A` on `pk` against the oracles, and
output `D`'s verdict on `(a, m, (d_i)_i, σ)`, where `d_i` is `COPY` on a copy of the challenge. -/
noncomputable def snmReal (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl : ℕ) (D : NUPPT)
    (n : ℕ) : ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
  (ProbComp.sample (A.Coins n)).bind fun rA =>
  (ProbComp.sample (D.Coins n)).bind fun rD =>
  (simulate
      (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ)
      (A.toCompOn (S.snmCodec M n r sl) n q (pairFstD (S.gen.runAt n [] rg)) rA) none).bind
    fun res =>
      let a := (res.2.map Prod.snd).getD (zeroBits _)
      .pure (D.distinguisherL n
        (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
          (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg))
            (decide (res.2.map Prod.fst = some (S.snmCt res.1 i))) (S.snmCt res.1 i))
          (snmSigma res.1)) rD)

/-- The real simulation experiment samples all coins, runs the adversary against its oracles,
and applies the distinguisher to the resulting parameter, message, entries, and final output
[PSV07, Definition 1]. -/
theorem snmReal_eq (atk : Attack) (M : MsgSampler) (A : NUPPT) (q r sl : ℕ) (D : NUPPT)
    (n : ℕ) :
    S.snmReal atk M A q r sl D n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
      (ProbComp.sample (A.Coins n)).bind fun rA =>
      (ProbComp.sample (D.Coins n)).bind fun rD =>
      (simulate
          (S.snmImpl atk M n (pairFstD (S.gen.runAt n [] rg)) (pairSndD (S.gen.runAt n [] rg)) ρ)
          (A.toCompOn (S.snmCodec M n r sl) n q (pairFstD (S.gen.runAt n [] rg)) rA) none).bind
        fun res =>
          let a := (res.2.map Prod.snd).getD (zeroBits (M.paramLen.eval n))
          .pure (D.distinguisherL n
            (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
              (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg))
                (decide (res.2.map Prod.fst = some (S.snmCt res.1 i))) (S.snmCt res.1 i))
              (snmSigma res.1)) rD)) := rfl

/-! ### The ideal experiment -/

/-- **The oracle of the ideal experiment**: on the parameter `a` (the first one asked, recorded),
the history `h(m)` of `m = M(a; ρ)`. -/
noncomputable def simImpl (M : MsgSampler) (n : ℕ) (ρ : M.samp.Coins n) :
    QueryImpl (M.simSpec n) (Option (Fin (M.paramLen.eval n) → Bool)) unifSpec :=
  fun _ a s => .pure (M.histAt n (M.draw (S.msgLen.eval n) n (s.getD a) ρ), some (s.getD a))

/-- The ideal oracle returns the history of the sampled message at the recorded parameter,
or at the current query if no parameter has been recorded, and records that parameter. -/
theorem simImpl_eq (M : MsgSampler) (n : ℕ) (ρ : M.samp.Coins n) :
    S.simImpl M n ρ =
      fun _ a s => .pure
        (M.histAt n (M.draw (S.msgLen.eval n) n (s.getD a) ρ), some (s.getD a)) := rfl

/-- The codec of the simulator: its one oracle, and a final output of `r` entries, each a `COPY`
flag and a ciphertext, followed by an `sl`-bit `σ`. -/
def simCodec (M : MsgSampler) (n r sl : ℕ) :
    MachineCodec (M.simSpec n) (Fin (r * (S.ctLen.eval n + 1) + sl) → Bool) :=
  bitCodec (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl)

/-- The ideal-experiment codec uses `decodeBitMove` with parameter and history lengths and
`r * (ctLen(n) + 1) + sl` output bits. -/
theorem simCodec_decodeMove (M : MsgSampler) (n r sl : ℕ) (w : List Bool) :
    (S.simCodec M n r sl).decodeMove w =
      decodeBitMove (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
        (r * (S.ctLen.eval n + 1) + sl) w :=
  bitCodec_decodeMove (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl) w

/-- The ideal-experiment codec encodes a log entry `(i, x, y)` as `⟨1^i, ⟨x, y⟩⟩`. -/
theorem simCodec_encodeEntry (M : MsgSampler) (n r sl : ℕ)
    (e : Σ i, (M.simSpec n).dom i × (M.simSpec n).rng i) :
    (S.simCodec M n r sl).encodeEntry e =
      pairEncode (List.replicate e.1 true) (pairEncode (List.ofFn e.2.1) (List.ofFn e.2.2)) :=
  bitCodec_encodeEntry (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl) e

/-- When its query budget expires, the ideal-experiment codec returns
`zeroBits (r * (ctLen(n) + 1) + sl)`. -/
theorem simCodec_timeout (M : MsgSampler) (n r sl : ℕ) :
    (S.simCodec M n r sl).timeout = zeroBits (r * (S.ctLen.eval n + 1) + sl) :=
  bitCodec_timeout (fun _ => M.paramLen.eval n) (fun _ => M.histLen.eval n)
    (r * (S.ctLen.eval n + 1) + sl)

/-- The `i`-th entry of the simulator's output: its `COPY` flag and its ciphertext. -/
def simEntry {n r sl : ℕ} (w : Fin (r * (S.ctLen.eval n + 1) + sl) → Bool) (i : Fin r) :
    Bool × (Fin (S.ctLen.eval n) → Bool) :=
  (w (Fin.castAdd sl (finProdFinEquiv (i, 0))),
    fun j => w (Fin.castAdd sl (finProdFinEquiv (i, j.succ))))

attribute [simps (config := { isSimp := false }) fst snd] simEntry

/-- **The ideal experiment** `SIM-NME′‾(Π, S, n)` [PSV07, Definition 1, `ℓ = 1`] for the sampler
`M`, `r` output entries and an `sl`-bit `σ`, followed by the distinguisher `D`: sample the keys
and the coins, run the simulator on `pk` against the history oracle with one query, and output
`D`'s verdict on `(a, m, (d_i)_i, σ)`, where `d_i` is `COPY` on a flagged entry and `Dec_sk(c_i)`
otherwise. -/
noncomputable def snmIdeal (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (D : NUPPT) (n : ℕ) :
    ProbComp Bool :=
  (ProbComp.sample (S.gen.Coins n)).bind fun rg =>
  (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
  (ProbComp.sample (Sim.Coins n)).bind fun rS =>
  (ProbComp.sample (D.Coins n)).bind fun rD =>
  (simulate (S.simImpl M n ρ)
      (Sim.toCompOn (S.simCodec M n r sl) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none).bind
    fun res =>
      let a := res.2.getD (zeroBits _)
      .pure (D.distinguisherL n
        (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
          (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg)) (S.simEntry res.1 i).1
            (S.simEntry res.1 i).2)
          (snmSigma res.1)) rD)

/-- The ideal simulation experiment samples all coins, runs the simulator against the history
oracle, and applies the distinguisher to the parameter, message, decoded entries, and final
output [PSV07, Definition 1]. -/
theorem snmIdeal_eq (M : MsgSampler) (Sim : NUPPT) (r sl : ℕ) (D : NUPPT) (n : ℕ) :
    S.snmIdeal M Sim r sl D n =
      (ProbComp.sample (S.gen.Coins n)).bind (fun rg =>
      (ProbComp.sample (M.samp.Coins n)).bind fun ρ =>
      (ProbComp.sample (Sim.Coins n)).bind fun rS =>
      (ProbComp.sample (D.Coins n)).bind fun rD =>
      (simulate (S.simImpl M n ρ)
          (Sim.toCompOn (S.simCodec M n r sl) n 1 (pairFstD (S.gen.runAt n [] rg)) rS) none).bind
        fun res =>
          let a := res.2.getD (zeroBits (M.paramLen.eval n))
          .pure (D.distinguisherL n
            (S.snmView a (M.draw (S.msgLen.eval n) n a ρ)
              (fun i => S.snmEntry (pairSndD (S.gen.runAt n [] rg)) (S.simEntry res.1 i).1
                (S.simEntry res.1 i).2)
              (snmSigma res.1)) rD)) := rfl

/-! ### Definition 173.7 and Theorem 174.8 -/

/-- **Simulation-based non-malleability** [PS10, Definition 173.7], in the form SIM-NME′ of
[PSV07, Definition 1] at one message, under the attack `atk`: for every sampler `M` (with its
history function), every non-uniform PPT adversary `A`, every polynomial query budget `q`,
number `r` of output ciphertexts and length `sl` of `σ`, there is a non-uniform PPT simulator
whose ideal experiment every non-uniform PPT distinguisher tells from `A`'s real one with
negligible advantage. -/
def SimNMSecure (atk : Attack) : Prop :=
  ∀ (M : MsgSampler) (A : NUPPT) (q r sl : PolyExpr), ∃ Sim : NUPPT,
    ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
      advantage (S.snmReal atk M A (q.eval n) (r.eval n) (sl.eval n) D n)
        (S.snmIdeal M Sim (r.eval n) (sl.eval n) D n) ≤ ε n

/-- Simulation-based non-malleability holds exactly when, for every sampler, adversary and
polynomial budgets, one simulator makes every distinguisher's real/ideal advantage negligible
[PS10, Definition 173.7; PSV07, Definition 1]. -/
theorem SimNMSecure_iff (atk : Attack) :
    S.SimNMSecure atk ↔
      ∀ (M : MsgSampler) (A : NUPPT) (q r sl : PolyExpr), ∃ Sim : NUPPT,
        ∀ D : NUPPT, ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n,
          advantage (S.snmReal atk M A (q.eval n) (r.eval n) (sl.eval n) D n)
            (S.snmIdeal M Sim (r.eval n) (sl.eval n) D n) ≤ ε n := Iff.rfl

/-- **Theorem 174.8, (relation-based ⇒ indistinguishability-based), for every attack**
[PSV07, Corollary 1, at one message]: SIM-NME′ implies Definition 172.6.

**Proof sketch** (the maintainer's; [PSV07] defers its proof).
1. Fix an NM adversary `A` (budget `q`, `ℓ` ciphertexts) and a distinguisher `D`. Take the
   sampler `M` with parameter `⟨m₀, m₁⟩` that outputs `m_β` for a uniform coin `β`, and the
   constant history. The adversary `A'` runs `A`, forwarding `Dec`; on `A`'s challenge
   `⟨m₀, m₁⟩` it asks its own challenge with that parameter and passes `y` on. It outputs `A`'s
   ciphertexts, with `sl = 0`.
2. In the real experiment `m = m_β`, `y ← Enc_pk(m_β)`, and the entries `d_i` are `NM_β`'s
   output once `COPY` is read as `⊥`. Let `D'` read `m₀, m₁, m` from the view, output `0` when
   `m₀ = m₁`, and otherwise output whether `D`'s verdict on the converted entries equals `β`.
   Then `Pr[D' = 1] = ½ + ½ (Pr[D(NM_1) = 1] − Pr[D(NM_0) = 1])` on the event `m₀ ≠ m₁`
   (when `m₀ = m₁`, `NM_0` and `NM_1` coincide).
3. In the ideal experiment the simulator's entries depend on `pk`, its coins and the constant
   history, so they are independent of `β` given the parameter; `D'` accepts with probability
   `½` on the event `m₀ ≠ m₁`. The distinguisher `D''` that tests `m₀ ≠ m₁` bounds the
   difference of that event's probabilities. So `NM`'s advantage is at most twice the sum of
   `D'`'s and `D''`'s, both negligible. -/
theorem nmSecure_of_simNMSecure (atk : Attack) (h : S.SimNMSecure atk) : S.NMSecure atk := by
  sorry

/-- **Theorem 174.8, (indistinguishability-based ⇒ relation-based), under CPA** [PSV07,
Theorem 3, at one message]: Definition 172.6 implies SIM-NME′ under a chosen-plaintext attack.
(Under CCA1 and CCA2 it does not, [PSV07, Theorem 4].)

**Proof sketch** (the maintainer's; [PSV07] defers its proof). Fix `M`, `A`, `q`, `r`, `sl`.
1. **The simulator** runs `A` on `pk`, answering `Dec` with `⊥` (CPA, `snmImpl_dec_cpa`). On
   `A`'s challenge `a` it asks its own query `a`, gets `h(m)`, draws a dummy `m̃ ← M(a)` with its
   own coins (it can run `M`), and answers `A` with `⟨Enc_pk(m̃), h(m)⟩`. It outputs `A`'s
   ciphertexts, flagging those equal to its dummy challenge, and `σ`. If `A` never asks, it
   never queries and outputs `A`'s output unflagged. At `msgLen(n) = 0` the two experiments
   coincide.
2. **The two experiments differ only in the challenge**: `Enc_pk(m)` in the real one,
   `Enc_pk(m̃)` in the ideal one, with `m, m̃` independent draws from `M(a)`, and the same `h(m)`.
3. **The NM adversary** `B` runs `A`; at `a` it draws `m, m̃ ← M(a)`, asks its challenge on
   `⟨m, m̃⟩`, receives `y = Enc_pk(m_b)`, and answers `A` with `⟨y, h(m)⟩`. It outputs `A`'s
   ciphertexts, then for each bit `x` of `a`, `m`, `σ` and the copy flags `[c_i = y]`, the pair
   `Enc_pk(x^{msgLen})`, `Enc_pk((¬x)^{msgLen})`. The two plaintexts differ, so by correctness at
   most one of the pair is the challenge, and the NM view yields `x` (as in the sketch of
   Theorem 175.9).
4. From `NM_b`'s view, the distinguisher reconstructs `(a, m, (d_i)_i, σ)`: the real experiment's
   output for `b = 0`, and the ideal one's (with the simulator of step 1) for `b = 1`. So `D`'s
   advantage is `B`'s NM advantage, negligible. -/
theorem simNMSecure_of_nmSecure_cpa (h : S.NMSecure .cpa) : S.SimNMSecure .cpa := by
  sorry

/-- **Theorem 174.8 under CPA** [PS10, Theorem 174.8; PSV07, Theorem 3, at one message]:
non-malleability (Definition 172.6) and simulation-based non-malleability (Definition 173.7, as
SIM-NME′) coincide under a chosen-plaintext attack. -/
theorem simNMSecure_cpa_iff_nmSecure_cpa : S.SimNMSecure .cpa ↔ S.NMSecure .cpa :=
  ⟨S.nmSecure_of_simNMSecure .cpa, S.simNMSecure_of_nmSecure_cpa⟩

end FixedLengthPKScheme

end TCSlib.Cryptography.Composability
