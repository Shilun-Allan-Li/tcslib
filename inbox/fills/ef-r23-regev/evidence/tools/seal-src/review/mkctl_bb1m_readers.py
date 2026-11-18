"""mkctl_bb1m_readers.py (fill bb1-machine, Claude lead, 2026-11-16): mkctl_bb1m.py with the harness unchanged
(assemble, the covering-subset choice of seal records, the plan format, namespace PairingControls) and seven rows
added, one per approved reader, each a negative (the unfolding the reader replaces, stated in a consumer's context:
the reader's own statement, `type_of%` of the reader, proved by the owner's own proof term) and a positive (the
reader): IBEScheme.oracleImpl (oracleImpl_zero_onSpec, oracleImpl_one_onSpec, oracleImpl_two_onSpec; negative
`(OracleComp.bind_pure _).symm`), bb1Scheme (ofFn_bb1Scheme_encPP and ofFn_bb1Scheme_encSK, negative `rfl`;
bb1Scheme_msgSpace_iff, negative `exists_congr fun _ => List.ofFn_inj.symm`) and bb1SimCt (ofFn_bb1SimCt, negative
`by rw [padFin_ofFn]; rfl`). The fill adds no new definition, so no helper-definition row is added. The covering
subset picks, per target and variant, the sealed owner with the fewest requests containing it (a consumer of
Defs/BonehBoyen, where these definitions are foreign). Previous header (mkctl_bb1m.py) follows.
mkctl_bb1m.py (fill-bb1-machine, unit bb1-machine, T4): mkctl_pbdh.py with the harness unchanged (assemble, the
covering-subset choice of seal records, the plan format, namespace PairingControls) and thirteen rows added for
definitions foreign to the sealed owners of this fill (the helper modules under BonehBoyenMachine/ and the owned
BonehBoyenMachine.lean) that their proofs read only through published readers: IBEScheme.inLens (inLens_zero),
IBEScheme.outLens (outLens_two), Pairing.tupleStr (tupleStr_eq), BB1.idToZ (idToZ_eq), Games.PolyHandler.input
(input_eq), ETTGame.tapeImpl (tapeImpl_apply), and the helper definitions BB1Machine.qLen (qLen_zero), BB1Machine.draw
(draw_eq; Draws, foreign to Words/Handler/Reduction), BB1Machine.sJ, BB1Machine.kT, BB1Machine.blkS, BB1Machine.uS
(sJ_eq, kT_eq, blkS_eq, uS_eq; Words, foreign to Handler/Reduction) and BB1Machine.handler (handler_seedLen; Handler,
foreign to Reduction); each negative the rfl unfolding, each positive the reader (stated as `type_of%` of the reader
where the statement is long, as in the sidImpl row). The pbdh rows are kept verbatim (rows whose target is in no
sealed request set are not exercised).
Previous header (mkctl_pbdh.py) follows.
mkctl_pbdh.py (fill-pair-bdh, unit pair-bdh, T1): mkctl_g40.py with the harness unchanged (assemble, the covering-subset
choice of seal records, the plan format, namespace PairingControls) and nine rows added to B for definitions foreign to
the sealed owner Pairing/Assumptions that the T1 proof reads only through their published readers: NUPPT.distinguisherL
(distinguisherL_eq), NUPPT.runAtL (runAtL_eq), NUPPT.layout (layout_eq), NUPPT.ofPolyTime (coins_ofPolyTime),
NUPPT.advInput (advInput_eq), Games.accept (accept_eq), uprob (uprob_def), BilinearGen.OrderAtLeastExcept
(orderAtLeastExcept_iff), BilinearGen.inst (inst_eq); each negative the rfl/Iff.rfl unfolding, each positive the reader.
The LE-gate40 rows are kept verbatim (rows whose target is in no sealed request set are not exercised).
Previous header (mkctl_g40.py) follows.
mkctl_g40.py (LE-gate40, pairing statements PR #331): mkctl_g36.py with the harness unchanged
(assemble, the covering-subset choice of seal records, the plan format) and the rows B replaced by
pairing rows, each a negative rfl/Iff.rfl unfolding of a definition foreign to some sealed owner
and a positive through its published reader: PolyExpr.eval (B only), padFin (padFin_def),
OracleComp.AllOutputs (allOutputs_pure), BilinearGen.desc (desc_eq), BilinearGen.DBDHAssumption
(dbdhAssumption_iff), IBEScheme.Correct (correct_iff), IBEScheme.sidImpl (sidImpl_init_none),
BB1.F (F_eq), KeyExchange.jouxMsg (jouxMsg_eq); namespace PairingControls.
Attempt 2: the sidImpl row is stated as `type_of% (S.sidImpl_init_none …)`; attempt 1 restated the
equation, whose oracle-0 query and answer types only check by unfolding `inLens`/`outLens` (sealed
foreign definitions of the control file), so both of its theorems failed twice under the seal (a
control-statement defect, not a module finding; rule10/controls-attempt1/).
Previous header (mkctl_g36.py) follows.
mkctl_g36.py (LE-gate36): mkctl_sg.py unchanged except one added row B[PrivateKeyScheme.encodeList]
(negative: the rfl unfolding on a cons; positive: the published reader PrivateKeyScheme.encodeList_cons), the definition
under the G36-01 lemma `length_le_length_encodeList`. Previously mkctl_sg.py (sc-garble review): mkctl_scot.py with sc-garble rows (PolyExpr.eval, the FinDist CoeFun instance,
DAGCircuit.IsFaninTwo (the approved reader), spEncStr, sliceEnc, Good, and the helper definitions sliceMask (Pad),
SliceReduction.slicePost (SliceParser) and SpecialWrongKey.prefixTest (WrongKey), foreign to their later consumers;
each negative the rfl/Iff.rfl unfolding, each positive its published reader) and namespace ScGarbleControls.
Attempt 2: per-row `open … in` prefixes (the IsFaninTwo row opens only BoolCircuit, the Good row BoolCircuit and
SecureComputation), because Turing is not in Garbling's import closure (attempt 1: unknown namespace in the Garbling probes).
Previously mkctl_scot.py (sc-ot review): mkctl_learning.py with sc-ot rows (PolyExpr.eval, the FinDist CoeFun
instance, NUPPT.layout, Strategy.encodeMsgs, otFunctionality, and the helper definitions OT.mask, OT.simSeg, OT.inA2,
OT.bobView, OT.hcBit, foreign to the later helpers and the owned file; each negative the rfl unfolding, each positive
its published reader) and namespace ScGarbleControls. Previously: mkctl_learning.py (learning-r1 review): mkctl_lamport.py with learning rows (PolyExpr.eval, FinDist.uniform, the FinDist
CoeFun instance, PAC.label, uprob, acceptProb, and the helper definitions LearnPRF.firstBit, tupleWord, learnerFn,
foreign to the later helpers and the owned file) and namespace LearningControls. Previously: mkctl_lamport.py (lamport review): mkctl_dlcrh.py with lamport rows (padFin, PolyExpr.eval, ProbComp.expect, ProbComp.sample, OracleComp.bind (the three names of the patch-4 opacity block), LamportFill.secretWord, LamportFill.signatureBlock, LamportMachine.u). Previously: mkctl_dlcrh.py (dl-crh review): mkctl_extnosrc.py with dl-crh rows (padFin, PolyExpr.eval, Authentication.splitBits, Candidates.expSampleRaw (new reader expSampleRaw_eq), FromDiscreteLog.modularDifference, FromDiscreteLog.residueFinEquiv). Previously: mkctl_extnosrc.py: mkctl_dlfolds.py with ext-nosrc rows (padFin, PolyExpr.eval, FinDist.uniform, the FinDist CoeFun instance, Rejection.mixture, Rejection.select). Previously: mkctl_dlfolds.py: mkctl_dl.py with the dl-folds rows (iterEmit, rAns, finA, cntRead, ansRead, coinBlock, fwdHandler, logEmit, chunkMap, PolyExpr.eval, padFin). Original: mkctl_dl.py (attempt 2: rU negative row is the bare unfolding `rU w = pairFstD (pairFstD w)`; attempt 1 used `rU (input ..) = 1^n`, not rfl-true unsealed): the nm-cca2 review mkctl.py (verbatim harness) with dl-consolidation rows B (head names: Games.castImpl,
FunFamily.blocks, EnsembleLemmas.padL, xorPerm, InteractiveHandler.rU, PK/SK indCodec, splitHalf, ChallengeSim.chRun,
plus padFin, zeroBits, PolyExpr.eval) and a covering subset of seal records (see below). Original header follows.
mkctl.py <archived-tools-dir> <seals-dir> <worktree> <probe-subdir> <outdir>
nm-cca2 review (attempt 3: PK indImpl row stated at the spec type, as in the pk-cpa-cca1 attempt 2): the pk-cpa-cca1 review mkctl.py with its own rows B (below; the generic pairEncode/padFin/zeroBits/simulate/
inLens/acDin/castImpl/seedIn/decAnswer/decOpen rows kept verbatim, plus PK outLens, PK indImpl, PolyExpr.eval, InteractiveHandler.finInput
and the NMCCA2 helper definitions fwdHandler, finU, logEmit, cntRead, decHandler, encHandler, guessBit), seal records Seal?_*.json
(A = PolyExpr.eval exempt, B = sealed) and namespace NmControls. Original header:
Sensitivity controls for the pk-cpa-cca1 review (the bitwise-cpa review's mkctl.py with the not-cca2 review's inLens/decAnswer/prfScheme rows
and rows for the PRFGame helper definitions (attempt 2: pkHState/pkSeedTapes rows dropped, indImpl row stated at the spec type), FixedLengthScheme.indImpl and decOpen appended to B; bitwise-cpa header follows:
B keeps every adaptive-cpa row and adds padCt, seedIn, coinBlock, blockState, PublicKeyScheme.padded, BitPublicKeyScheme.bitwise, and the
BitwiseSim rows qDin, qHandler, plantAns (foreign to BitwiseCPA.lean only); originally:
B keeps the pairEncode/padFin/zeroBits rows, the padded-cpa chRun/recAdvIn rows, and adds simulate, PK inLens and seven AdaptiveCPA rows), built like levin/final/tools/mkcontrols.py
(same archived harness: build_seals.seal_command via request_payload_adapter). For each whole-file
seal record Seal_<F>.json: ControlS_<F> imports F and installs F's exact request set, then body
readings (negative: must fail exactly once sealed) and published-reader positives; ControlU_<F> is
the same without the seal (all must pass). Bodies are chosen by which definitions F's request set
contains (see B)."""
import sys, json, importlib.util
from pathlib import Path
tools, sealdir, wt, sub, outdir = sys.argv[1:6]
sys.dont_write_bytecode = True
def load(path, name):
    spec = importlib.util.spec_from_file_location(name, path); m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m); return m
bs = load(Path(tools) / 'build_seals.py', 'levin_bs'); controls = load(Path(tools) / 'build_controls.py', 'levin_controls')
adapter = load(Path(tools) / 'request_payload_adapter.py', 'levin_adapter'); adapter.configure_builders(bs, controls)
import os
CHUNK = int(os.environ.get('SEAL_CHUNK', '0'))
if CHUNK:
    _orig = bs.seal_command
    def _chunked(label, rows, *, end):
        if len(rows) <= CHUNK: return _orig(label, rows, end=end)
        return b''.join(_orig(f'{label}_part{i // CHUNK + 1}', rows[i:i + CHUNK], end=end) for i in range(0, len(rows), CHUNK))
    bs.seal_command = _chunked
G = 'TCSlib.Cryptography.Games'
P = 'TCSlib.Cryptography.Pairing'
IB = 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased'
def row(name, neg_body, pos_body):
    return [(name, True, neg_body), (name + "Reader", False, pos_body)]
O1 = "open TCSlib.Cryptography in\n"
OG = "open TCSlib.Cryptography.Games in\n"
OP2 = "open Complexity TCSlib.Cryptography TCSlib.Cryptography.Pairing in\n"
OI = "open TCSlib.Cryptography.AdvancedEncryption.IdentityBased in\n"
OF = "open TCSlib.Cryptography.Pairing TCSlib.Cryptography.AdvancedEncryption.IdentityBased in\n"
OK = "open TCSlib.Cryptography.Pairing TCSlib.Cryptography.KeyExchange in\n"
DB = "G.DBDHAssumption ↔ ∀ D : NUPPT, Negligible fun κ => G.dbdhAdv D κ"
COR = ("S.Correct ↔ ∀ κ (id : Fin (S.idLen.eval κ) → Bool) (m : Fin (S.msgLen.eval κ) → Bool),\n"
       "      (S.honestRun κ id m).AllOutputs fun x =>\n"
       "        S.MsgSpace κ x.1 m → S.dec κ x.2.1 x.2.2 = some m")
SIDARGS = ("(S : IBEScheme) (b : Bool) (κ : ℕ) (pp : S.PP κ) (msk : S.MSK κ)\n"
           "    (id : Fin (S.idLen.eval κ) → Bool) (c : Option (Fin (S.ctLen.eval κ) → Bool))")
SID = "S.sidImpl b κ pp msk 0 id (none, c) = .pure (S.encPP κ pp, (some id, c))"
B = {
 'Complexity.PolyExpr.eval': row("ctlEval",
   "theorem ctlEval (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := rfl\n",
   "theorem ctlEvalReader (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 :=\n  Complexity.PolyExpr.eval_const 2 n\n"),
 'TCSlib.Cryptography.padFin': row("ctlPadFin",
   O1 + "theorem ctlPadFin (ℓ : ℕ) (w : List Bool) :\n    padFin ℓ w = (fun i => w.getD i false : Fin ℓ → Bool) := rfl\n",
   O1 + "theorem ctlPadFinReader (ℓ : ℕ) (w : List Bool) :\n    padFin ℓ w = (fun i => w.getD i false : Fin ℓ → Bool) :=\n  padFin_def ℓ w\n"),
 G + '.OracleComp.AllOutputs': row("ctlAllOutputs",
   OG + "theorem ctlAllOutputs {α : Type} (P : α → Prop) (a : α) :\n    (OracleComp.pure (spec := unifSpec) a).AllOutputs P ↔ P a := Iff.rfl\n",
   OG + "theorem ctlAllOutputsReader {α : Type} (P : α → Prop) (a : α) :\n    (OracleComp.pure (spec := unifSpec) a).AllOutputs P ↔ P a :=\n  OracleComp.allOutputs_pure\n"),
 P + '.BilinearGen.desc': row("ctlDesc",
   OP2 + "theorem ctlDesc (G : BilinearGen) (κ : ℕ) (r : G.gen.Coins κ) :\n    G.desc κ r = G.gen.runAt κ [] r := rfl\n",
   OP2 + "theorem ctlDescReader (G : BilinearGen) (κ : ℕ) (r : G.gen.Coins κ) :\n    G.desc κ r = G.gen.runAt κ [] r :=\n  G.desc_eq κ r\n"),
 P + '.BilinearGen.DBDHAssumption': row("ctlDBDH",
   OP2 + f"theorem ctlDBDH (G : BilinearGen) :\n    {DB} := Iff.rfl\n",
   OP2 + f"theorem ctlDBDHReader (G : BilinearGen) :\n    {DB} :=\n  G.dbdhAssumption_iff\n"),
 IB + '.IBEScheme.Correct': row("ctlCorrect",
   OI + f"theorem ctlCorrect (S : IBEScheme) :\n    {COR} := Iff.rfl\n",
   OI + f"theorem ctlCorrectReader (S : IBEScheme) :\n    {COR} :=\n  S.correct_iff\n"),
 IB + '.IBEScheme.sidImpl': row("ctlSidImpl",
   OI + f"theorem ctlSidImpl {SIDARGS} :\n    type_of% (S.sidImpl_init_none b κ pp msk id c) := rfl\n",
   OI + f"theorem ctlSidImplReader {SIDARGS} :\n    type_of% (S.sidImpl_init_none b κ pp msk id c) :=\n  S.sidImpl_init_none b κ pp msk id c\n"),
 IB + '.BB1.F': row("ctlF",
   OF + "theorem ctlF {wG wT : ℕ} {B : BilinearGroup wG wT} (pp : BB1.Params B) (x : ZMod B.order) :\n    BB1.F pp x = pp.g1 ^ x.val * pp.h := rfl\n",
   OF + "theorem ctlFReader {wG wT : ℕ} {B : BilinearGroup wG wT} (pp : BB1.Params B) (x : ZMod B.order) :\n    BB1.F pp x = pp.g1 ^ x.val * pp.h :=\n  BB1.F_eq pp x\n"),
 'TCSlib.Cryptography.KeyExchange.jouxMsg': row("ctlJouxMsg",
   OK + "theorem ctlJouxMsg {wG wT : ℕ} (B : BilinearGroup wG wT) (g : B.G) (x : ZMod B.order) :\n    jouxMsg B g x = g ^ x.val := rfl\n",
   OK + "theorem ctlJouxMsgReader {wG wT : ℕ} (B : BilinearGroup wG wT) (g : B.G) (x : ZMod B.order) :\n    jouxMsg B g x = g ^ x.val :=\n  jouxMsg_eq B g x\n"),
 'Complexity.NUPPT.distinguisherL': row("ctlDistL",
   "open Complexity in\ntheorem ctlDistL (A : NUPPT) (n : ℕ) (w : List Bool) (r : A.Coins n) :\n    A.distinguisherL n w r = decide (A.runAt n w r = [true]) := rfl\n",
   "open Complexity in\ntheorem ctlDistLReader (A : NUPPT) (n : ℕ) (w : List Bool) (r : A.Coins n) :\n    A.distinguisherL n w r = decide (A.runAt n w r = [true]) :=\n  A.distinguisherL_eq n w r\n"),
 'Complexity.NUPPT.runAtL': row("ctlRunAtL",
   "open Complexity Turing in\ntheorem ctlRunAtL (A : NUPPT) (n : ℕ) (y r : List Bool) :\n    A.runAtL n y r = A.output (pairEncode (pairEncode (NUPPT.advInput n y) (A.advice n)) r) := rfl\n",
   "open Complexity Turing in\ntheorem ctlRunAtLReader (A : NUPPT) (n : ℕ) (y r : List Bool) :\n    A.runAtL n y r = A.output (pairEncode (pairEncode (NUPPT.advInput n y) (A.advice n)) r) :=\n  A.runAtL_eq n y r\n"),
 'Complexity.NUPPT.layout': row("ctlLayout",
   "open Complexity Turing in\ntheorem ctlLayout (u y α r : List Bool) :\n    NUPPT.layout u y α r = pairEncode (pairEncode (pairEncode u y) α) r := rfl\n",
   "open Complexity Turing in\ntheorem ctlLayoutReader (u y α r : List Bool) :\n    NUPPT.layout u y α r = pairEncode (pairEncode (pairEncode u y) α) r :=\n  NUPPT.layout_eq u y α r\n"),
 'Complexity.NUPPT.ofPolyTime': row("ctlOfPolyTime",
   "open Complexity in\ntheorem ctlOfPolyTime {f : List Bool → List Bool} (hf : PolyTimeComputable f) (coins adv : PolyExpr)\n    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :\n    (NUPPT.ofPolyTime hf coins adv advice hα).coins = coins := rfl\n",
   "open Complexity in\ntheorem ctlOfPolyTimeReader {f : List Bool → List Bool} (hf : PolyTimeComputable f) (coins adv : PolyExpr)\n    (advice : ℕ → List Bool) (hα : ∀ n, (advice n).length ≤ adv.eval n) :\n    (NUPPT.ofPolyTime hf coins adv advice hα).coins = coins :=\n  NUPPT.coins_ofPolyTime hf coins adv advice hα\n"),
 'Complexity.NUPPT.advInput': row("ctlAdvInput",
   "open Complexity Turing in\ntheorem ctlAdvInput (n : ℕ) (y : List Bool) :\n    NUPPT.advInput n y = pairEncode (List.replicate n true) y := rfl\n",
   "open Complexity Turing in\ntheorem ctlAdvInputReader (n : ℕ) (y : List Bool) :\n    NUPPT.advInput n y = pairEncode (List.replicate n true) y :=\n  NUPPT.advInput_eq n y\n"),
 G + '.accept': row("ctlAccept",
   OG + "theorem ctlAccept (c : ProbComp Bool) :\n    accept c = ProbComp.prob c (· = true) := rfl\n",
   OG + "theorem ctlAcceptReader (c : ProbComp Bool) :\n    accept c = ProbComp.prob c (· = true) :=\n  accept_eq c\n"),
 'TCSlib.Cryptography.uprob': row("ctlUprob",
   O1 + "theorem ctlUprob {α : Type} [Fintype α] (p : α → Prop) :\n    uprob p = (Nat.card {a // p a} : ℝ) / Fintype.card α := rfl\n",
   O1 + "theorem ctlUprobReader {α : Type} [Fintype α] (p : α → Prop) :\n    uprob p = (Nat.card {a // p a} : ℝ) / Fintype.card α :=\n  uprob_def p\n"),
 P + '.BilinearGen.OrderAtLeastExcept': row("ctlOrderAtLeast",
   OP2 + "theorem ctlOrderAtLeast (G : BilinearGen) (N : ℕ → ℕ) (δ : ℕ → ℝ) :\n    G.OrderAtLeastExcept N δ ↔\n      ∀ κ, uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < N κ) ≤ δ κ := Iff.rfl\n",
   OP2 + "theorem ctlOrderAtLeastReader (G : BilinearGen) (N : ℕ → ℕ) (δ : ℕ → ℝ) :\n    G.OrderAtLeastExcept N δ ↔\n      ∀ κ, uprob (fun r : G.gen.Coins κ => (G.inst κ r).order < N κ) ≤ δ κ :=\n  G.orderAtLeastExcept_iff N δ\n"),
 P + '.BilinearGen.inst': row("ctlInst",
   OP2 + "theorem ctlInst (G : BilinearGen) (κ : ℕ) (r : G.gen.Coins κ) :\n    G.inst κ r = G.group κ (G.desc κ r) := rfl\n",
   OP2 + "theorem ctlInstReader (G : BilinearGen) (κ : ℕ) (r : G.gen.Coins κ) :\n    G.inst κ r = G.group κ (G.desc κ r) :=\n  G.inst_eq κ r\n"),
}

MB = 'TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Machine'
OM = ("open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing "
      "TCSlib.Cryptography.Candidates TCSlib.Cryptography.AdvancedEncryption.IdentityBased "
      "TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BB1Machine in\n")
OT = "open TCSlib.Cryptography.Games TCSlib.Cryptography.Composability in\n"
def trow(name, args, reader):
    return row(name, f"{OM}theorem {name} {args} :\n    type_of% ({reader}) := rfl\n",
               f"{OM}theorem {name}Reader {args} :\n    type_of% ({reader}) :=\n  {reader}\n")
B.update({
 IB + '.IBEScheme.inLens': row("ctlInLens",
   OI + "theorem ctlInLens (S : IBEScheme) (κ : ℕ) : S.inLens κ 0 = S.idLen.eval κ := rfl\n",
   OI + "theorem ctlInLensReader (S : IBEScheme) (κ : ℕ) : S.inLens κ 0 = S.idLen.eval κ :=\n  S.inLens_zero κ\n"),
 IB + '.IBEScheme.outLens': row("ctlOutLens",
   OI + "theorem ctlOutLens (S : IBEScheme) (κ : ℕ) : S.outLens κ 2 = S.ctLen.eval κ := rfl\n",
   OI + "theorem ctlOutLensReader (S : IBEScheme) (κ : ℕ) : S.outLens κ 2 = S.ctLen.eval κ :=\n  S.outLens_two κ\n"),
 P + '.tupleStr': trow("ctlTupleStr",
   "{wG wT : ℕ} (B : BilinearGroup wG wT) (d : List Bool) (g x y z : B.G) (t : B.GT)",
   "tupleStr_eq B d g x y z t"),
 IB + '.BB1.idToZ': trow("ctlIdToZ",
   "{wG wT : ℕ} (B : BilinearGroup wG wT) {ℓ : ℕ} (id : Fin ℓ → Bool)", "BB1.idToZ_eq B id"),
 G + '.PolyHandler.input': trow("ctlInput",
   "(k n : ℕ) (z ω s : List Bool) (i : Fin k) (x : List Bool)",
   "PolyHandler.input_eq (k := k) n z ω s i x"),
 'TCSlib.Cryptography.Composability.ETTGame.tapeImpl': row("ctlTapeImpl",
   OT + "theorem ctlTapeImpl {ι : Type} {spec : OracleSpec ι} {σ τ : Type}\n"
   "    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ) (i : ι) (x : spec.dom i)\n"
   "    (s : σ) (j : ℕ) :\n    type_of% (ETTGame.tapeImpl_apply K T i x s j) := rfl\n",
   OT + "theorem ctlTapeImplReader {ι : Type} {spec : OracleSpec ι} {σ τ : Type}\n"
   "    (K : ∀ i, spec.dom i → σ → τ → ProbComp (spec.rng i × σ)) (T : ℕ → τ) (i : ι) (x : spec.dom i)\n"
   "    (s : σ) (j : ℕ) :\n    type_of% (ETTGame.tapeImpl_apply K T i x s j) :=\n"
   "  ETTGame.tapeImpl_apply K T i x s j\n"),
 MB + '.qLen': trow("ctlQLen", "(G : BilinearGen) (ℓ : PolyExpr)", "qLen_zero G ℓ"),
 MB + '.draw': trow("ctlDraw",
   "(G : BilinearGen) (κ : ℕ) (d : List Bool)\n    (w : Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool)",
   "draw_eq G κ d w"),
 MB + '.sJ': trow("ctlSJ", "(w : List Bool)", "sJ_eq w"),
 MB + '.kT': trow("ctlKT", "(w : List Bool)", "kT_eq w"),
 MB + '.blkS': trow("ctlBlkS", "(G : BilinearGen) (w : List Bool)", "blkS_eq G w"),
 MB + '.uS': trow("ctlUS", "(G : BilinearGen) (O : G.Ops) (w : List Bool)", "uS_eq G O w"),
 MB + '.handler': trow("ctlHandler",
   "(G : BilinearGen) (ℓ : PolyExpr) (O : G.Ops) (b : Bool) (q : PolyExpr) (H : ArithmeticFP)",
   "handler_seedLen G ℓ O b q H"),
})
OR = ("open Complexity TCSlib.Cryptography TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing "
      "TCSlib.Cryptography.AdvancedEncryption.IdentityBased in\n")
def rrow(name, args, reader, proof):
    return row(name, f"{OR}theorem {name} {args} :\n    type_of% ({reader}) :=\n  {proof}\n",
               f"{OR}theorem {name}Reader {args} :\n    type_of% ({reader}) :=\n  {reader}\n")
OIA = ("(S : IBEScheme) {σ : Type} (κ : ℕ)\n"
       "    (init : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.ppLen.eval κ) → Bool) × σ))\n"
       "    (key : (Fin (S.idLen.eval κ) → Bool) → σ → ProbComp ((Fin (S.skLen.eval κ + 1) → Bool) × σ))\n"
       "    (chal : (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool) → σ →\n"
       "      ProbComp ((Fin (S.ctLen.eval κ) → Bool) × σ))\n")
BP = "(OracleComp.bind_pure _).symm"
B.update({
 IB + '.IBEScheme.oracleImpl':
   rrow("ctlOracleZero", OIA + "    (x : (S.sidSpec κ).dom 0) (s : σ)",
        "S.oracleImpl_zero_onSpec κ init key chal x s", BP)
   + rrow("ctlOracleOne", OIA + "    (x : (S.sidSpec κ).dom 1) (s : σ)",
          "S.oracleImpl_one_onSpec κ init key chal x s", BP)
   + rrow("ctlOracleTwo", OIA + "    (x : (S.sidSpec κ).dom 2) (s : σ)",
          "S.oracleImpl_two_onSpec κ init key chal x s", BP),
 IB + '.bb1Scheme':
   rrow("ctlEncPP", "(G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)\n"
        "    (pp : BB1.Params (G.group κ d))", "ofFn_bb1Scheme_encPP G ℓ κ d pp", "rfl")
   + rrow("ctlEncSK", "(G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)\n"
          "    (k : BB1.Key (G.group κ d))", "ofFn_bb1Scheme_encSK G ℓ κ d k", "rfl")
   + rrow("ctlMsgSpace", "(G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)\n"
          "    (pp : BB1.Params (G.group κ d)) (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool)",
          "bb1Scheme_msgSpace_iff G ℓ κ d pp m", "exists_congr fun _ => List.ofFn_inj.symm"),
 IB + '.bb1SimCt':
   rrow("ctlSimCt", "(G : BilinearGen) (ℓ : PolyExpr) (κ : ℕ) (d : List Bool)\n"
        "    (Z : (G.group κ d).G) (T : (G.group κ d).GT) (α₁ : ZMod (G.group κ d).order)\n"
        "    (m : Fin ((bb1Scheme G ℓ).msgLen.eval κ) → Bool)",
        "ofFn_bb1SimCt G ℓ κ d Z T α₁ m", "by\n  rw [padFin_ofFn]\n  rfl"),
})
OP = ''
def assemble(label, module, rows, bodies, sealed):
    src = (f"import Lean\nimport {module}\n\nset_option maxHeartbeats 0\nset_option autoImplicit false\n"
           "set_option relaxedAutoImplicit false\n\n").encode()
    if sealed: src += bs.seal_command(label, rows, end=False)
    src += b"namespace PairingControls\n\n"
    expect = []
    for name, target, negative, body in bodies:
        start = src.count(b"\n") + 1
        src += body.encode() + b"\n"
        expect.append(dict(control=name, target=target, negative=negative, start_line=start,
                           end_line=start + body.count('\n') - 1))
    src += b"end PairingControls\n\n"
    if sealed: src += bs.seal_command(label, rows, end=True)
    return src, expect
out = Path(outdir); out.mkdir(parents=True, exist_ok=True); plan = []
# dl-consolidation review: controls only for a covering subset of the seal records: for each target of B
# (and each variant letter), the seal record with the fewest requests whose request set contains it.
recs = [json.load(open(p)) for p in sorted(Path(sealdir).glob('Seal*_*.json'))]
chosen = {}
for t in B:
    for letter in sorted({r['label'].split('_')[0][-1] for r in recs}):
        c = [r for r in recs if r['label'].split('_')[0][-1] == letter and t in {x['spelling'] for x in r['rows']}]
        if c:
            r = min(c, key=lambda r: (len(r['rows']), r['label'])); chosen[r['label']] = r
print('chosen', sorted(chosen))
for rec in [chosen[k] for k in sorted(chosen)]:
    module = rec['module']; rows = rec['rows']
    have = {r['spelling'] for r in rows}
    bodies = [(n, t, neg, b) for t, lst in B.items() if t in have for (n, neg, b) in lst]
    for sealed in (True, False):
        lab = ('ControlS_' if sealed else 'ControlU_') + rec['label'][4:]  # nm-cca2: keep the A/B letter of 'SealA_'/'SealB_'
        src, expect = assemble(lab, module, rows, bodies, sealed)
        p = Path(wt) / sub / (lab + '.lean'); p.parent.mkdir(parents=True, exist_ok=True); p.write_bytes(src)
        (out / (lab + '.lean.txt')).write_bytes(src)
        plan.append(dict(label=lab, module=f'{sub}/{lab}', owner=module, kind='own-seal', sealed=sealed,
                         requested=len(rows) if sealed else 0, controls=expect,
                         expected_errors=[e['start_line'] for e in expect if e['negative']] if sealed else []))
(out / 'controls-plan.json').write_text(json.dumps(plan, indent=1))
print(len(plan), 'control probes;', sum(len(p['expected_errors']) for p in plan), 'expected sealed failures')
