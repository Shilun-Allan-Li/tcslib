"""mkctl_g36.py (LE-gate36): mkctl_sg.py unchanged except one added row B[PrivateKeyScheme.encodeList]
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
FD = 'TCSlib.InformationTheory.FinDist'
SC = 'TCSlib.Cryptography.SecureComputation'
PE = 'Turing.pairEncode'
TC = 'TCSlib.Cryptography.TrapdoorCollection'
NU = 'Complexity.NUPPT'
def row(name, neg_body, pos_body):
    return [(name, True, neg_body), (name + "Reader", False, pos_body)]
O = "open Turing Complexity TCSlib.Cryptography TCSlib.Cryptography.SecureComputation in\n"
OB = "open BoolCircuit in\n"  # attempt 2: Turing is not in Garbling's closure
OG = "open BoolCircuit TCSlib.Cryptography.SecureComputation in\n"
SPENC = ("spEncStr E k m r = pairEncode r ((E (pairEncode k r)).take r.length ++\n"
         "      List.zipWith xor m ((E (pairEncode k r)).drop r.length))")
SLENC = ("sliceEnc G n o k r m =\n      spEncStr (fun _ => (List.ofFn (G n k r)).drop o) (List.ofFn k) m (List.ofFn r)")
SLARGS = ("{L : ℕ → ℕ} (G : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin (L n) → Bool))\n"
          "    (n o : ℕ) (k r : Fin n → Bool) (m : List Bool)")
MASK = ("sliceMask L n o m = padFin L (List.replicate (o + n) false ++ m ++\n"
        "      List.replicate (L - (o + n + m.length)) false)")
POST = "SliceReduction.slicePost z = Games.iterEmit SliceReduction.parserStep SliceReduction.parserEmit (z.length + 1) z"
PTEST = ("SpecialWrongKey.prefixTest E z =\n      [decide ((pairSndD (NUPPT.inArg z)).take (NUPPT.inParam z).length =\n"
         "        (E (pairEncode (NUPPT.inCoins z) (pairFstD (NUPPT.inArg z)))).take\n          (NUPPT.inParam z).length)]")
GOOD = ("Good M Cc s ↔\n      ∀ (i : Fin Cc.gates.length) (a : Fin (Cc.gates[i]).args.length → Bool),\n"
        "        (garbledTable M Cc s i).findSome? (M.dec (argKeys Cc s i a)) =\n"
        "          some (keyAt Cc s (n + i) (gateOut (Cc.gates[i]) a))")
GARGS = "{K C ρ : Type} [Inhabited K] {n : ℕ} (M : MultiEnc K C ρ) (Cc : DAGCircuit n)\n    (s : GarbleSeed Cc K ρ)"
FAN = ("C.IsFaninTwo ↔\n      (∀ g ∈ C.gates, g.args.Nodup ∧ (g.kind = .not → g.args.length = 1)) ∧\n"
       "        ∀ g ∈ C.gates, g.args.length ≤ 2")
B = {
 'Complexity.PolyExpr.eval': row("ctlEval",
   "theorem ctlEval (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := rfl\n",
   "theorem ctlEvalReader (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 :=\n  Complexity.PolyExpr.eval_const 2 n\n"),
 FD + '.instCoeFunForallReal': row("ctlCoe",
   f"theorem ctlCoe {{α : Type}} [Fintype α] (p : {FD} α) (a : α) : p a = p.prob a := rfl\n",
   f"theorem ctlCoeReader {{α : Type}} [Fintype α] (f : α → ℝ) (h₁ : ∀ a, 0 ≤ f a) (h₂ : ∑ a, f a = 1) (a : α) :\n    (⟨f, h₁, h₂⟩ : {FD} α) a = f a := {FD}.coe_mk f h₁ h₂ a\n"),
 'BoolCircuit.DAGCircuit.IsFaninTwo': row("ctlFanin",
   OB + f"theorem ctlFanin {{n : ℕ}} (C : DAGCircuit n) :\n    {FAN} := Iff.rfl\n",
   OB + f"theorem ctlFaninReader {{n : ℕ}} (C : DAGCircuit n) :\n    {FAN} :=\n  DAGCircuit.isFaninTwo_iff C\n"),
 SC + '.spEncStr': row("ctlSpEnc",
   O + f"theorem ctlSpEnc (E : List Bool → List Bool) (k m r : List Bool) :\n    {SPENC} := rfl\n",
   O + f"theorem ctlSpEncReader (E : List Bool → List Bool) (k m r : List Bool) :\n    {SPENC} :=\n  spEncStr_eq E k m r\n"),
 SC + '.sliceEnc': row("ctlSliceEnc",
   O + f"theorem ctlSliceEnc {SLARGS} :\n    {SLENC} := rfl\n",
   O + f"theorem ctlSliceEncReader {SLARGS} :\n    {SLENC} :=\n  sliceEnc_eq G n o k r m\n"),
 SC + '.sliceMask': row("ctlSliceMask",
   O + f"theorem ctlSliceMask (L n o : ℕ) (m : List Bool) :\n    {MASK} := rfl\n",
   O + f"theorem ctlSliceMaskReader (L n o : ℕ) (m : List Bool) :\n    {MASK} :=\n  sliceMask_eq L n o m\n"),
 SC + '.SliceReduction.slicePost': row("ctlSlicePost",
   O + f"theorem ctlSlicePost (z : List Bool) :\n    {POST} := rfl\n",
   O + f"theorem ctlSlicePostReader (z : List Bool) :\n    {POST} :=\n  SliceReduction.slicePost_eq z\n"),
 SC + '.SpecialWrongKey.prefixTest': row("ctlPrefixTest",
   O + f"theorem ctlPrefixTest (E : List Bool → List Bool) (z : List Bool) :\n    {PTEST} := rfl\n",
   O + f"theorem ctlPrefixTestReader (E : List Bool → List Bool) (z : List Bool) :\n    {PTEST} :=\n  SpecialWrongKey.prefixTest_eq E z\n"),
 'TCSlib.Cryptography.PrivateKeyScheme.encodeList': row("ctlEncList",
   O + "theorem ctlEncList (m : List Bool) (ms : List (List Bool)) :\n    PrivateKeyScheme.encodeList (m :: ms) = pairEncode m (PrivateKeyScheme.encodeList ms) := rfl\n",
   O + "theorem ctlEncListReader (m : List Bool) (ms : List (List Bool)) :\n    PrivateKeyScheme.encodeList (m :: ms) = pairEncode m (PrivateKeyScheme.encodeList ms) :=\n  PrivateKeyScheme.encodeList_cons m ms\n"),
 SC + '.Good': row("ctlGood",
   OG + f"theorem ctlGood {GARGS} :\n    {GOOD} := Iff.rfl\n",
   OG + f"theorem ctlGoodReader {GARGS} :\n    {GOOD} :=\n  good_iff M Cc s\n"),
}
OP = ''
def assemble(label, module, rows, bodies, sealed):
    src = (f"import Lean\nimport {module}\n\nset_option maxHeartbeats 0\nset_option autoImplicit false\n"
           "set_option relaxedAutoImplicit false\n\n").encode()
    if sealed: src += bs.seal_command(label, rows, end=False)
    src += b"namespace ScGarbleControls\n\n"
    expect = []
    for name, target, negative, body in bodies:
        start = src.count(b"\n") + 1
        src += body.encode() + b"\n"
        expect.append(dict(control=name, target=target, negative=negative, start_line=start,
                           end_line=start + body.count('\n') - 1))
    src += b"end ScGarbleControls\n\n"
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
