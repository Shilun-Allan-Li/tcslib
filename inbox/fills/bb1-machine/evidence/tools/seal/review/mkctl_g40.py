"""mkctl_g40.py (LE-gate40, pairing statements PR #331): mkctl_g36.py with the harness unchanged
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
}
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
