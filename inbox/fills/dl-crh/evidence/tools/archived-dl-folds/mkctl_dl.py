"""mkctl_dl.py (attempt 2: rU negative row is the bare unfolding `rU w = pairFstD (pairFstD w)`; attempt 1 used `rU (input ..) = 1^n`, not rfl-true unsealed): the nm-cca2 review mkctl.py (verbatim harness) with dl-consolidation rows B (head names: Games.castImpl,
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
CS = 'TCSlib.Cryptography.Composability.ChallengeSim'
AC = 'TCSlib.Cryptography.Composability.AdaptiveCPA'
PK = 'TCSlib.Cryptography.Composability.FixedLengthPKScheme'
SK = 'TCSlib.Cryptography.Composability.FixedLengthScheme'
G = 'TCSlib.Cryptography.Games'
IH = G + '.InteractiveHandler'
def row(name, neg_body, pos_body):
    return [(name, True, neg_body), (name + "Reader", False, pos_body)]
B = {
 'TCSlib.Cryptography.padFin': row("ctlPadFin",
   "theorem ctlPadFin (l : ℕ) (w : List Bool) (i : Fin l) :\n    TCSlib.Cryptography.padFin l w i = w.getD i false := rfl\n",
   "theorem ctlPadFinReader (l : ℕ) (w : List Bool) (i : Fin l) :\n    TCSlib.Cryptography.padFin l w i = w.getD i false := TCSlib.Cryptography.padFin_apply l w i\n"),
 G + '.zeroBits': row("ctlZeroBits",
   f"theorem ctlZeroBits (d : ℕ) (j : Fin d) : {G}.zeroBits d j = false := rfl\n",
   f"theorem ctlZeroBitsReader (d : ℕ) (j : Fin d) : {G}.zeroBits d j = false :=\n  {G}.zeroBits_apply d j\n"),
 'Complexity.PolyExpr.eval': row("ctlEval",
   "theorem ctlEval (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 := rfl\n",
   "theorem ctlEvalReader (n : ℕ) : (Complexity.PolyExpr.const 2).eval n = 2 :=\n  Complexity.PolyExpr.eval_const 2 n\n"),
 G + '.castImpl': row("ctlCastImpl",
   f"open {G} in\ntheorem ctlCastImpl {{k : ℕ}} {{σ : Type}} {{ins ins' outs outs' : Fin k → ℕ}}\n    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool) (s : σ) :\n    {G}.castImpl (ins := ins) (outs := outs) O i x s =\n      (O i (TCSlib.Cryptography.padFin (ins' i) (List.ofFn x)) s).bind fun p =>\n        .pure (TCSlib.Cryptography.padFin (outs i) (List.ofFn p.1), p.2) := rfl\n",
   f"open {G} in\ntheorem ctlCastImplReader {{k : ℕ}} {{σ : Type}} {{ins ins' outs outs' : Fin k → ℕ}}\n    (O : QueryImpl (bitSpec ins' outs') σ unifSpec) (i : Fin k) (x : Fin (ins i) → Bool) (s : σ) :\n    {G}.castImpl (ins := ins) (outs := outs) O i x s =\n      (O i (TCSlib.Cryptography.padFin (ins' i) (List.ofFn x)) s).bind fun p =>\n        .pure (TCSlib.Cryptography.padFin (outs i) (List.ofFn p.1), p.2) :=\n  {G}.castImpl_eq O i x s\n"),
 'TCSlib.Cryptography.FunFamily.blocks': row("ctlBlocks",
   "theorem ctlBlocks (q l : ℕ) (x : Fin (q * l) → Bool) (i : Fin q) (j : Fin l) :\n    TCSlib.Cryptography.FunFamily.blocks q l x i j = x (finProdFinEquiv (i, j)) := rfl\n",
   "theorem ctlBlocksReader (q l : ℕ) (x : Fin (q * l) → Bool) (i : Fin q) (j : Fin l) :\n    TCSlib.Cryptography.FunFamily.blocks q l x i j = x (finProdFinEquiv (i, j)) :=\n  TCSlib.Cryptography.FunFamily.blocks_apply q l x i j\n"),
 'TCSlib.Cryptography.EnsembleLemmas.padL': row("ctlPadL",
   "theorem ctlPadL (k : ℕ) (a : List Bool) :\n    List.ofFn (TCSlib.Cryptography.padFin k a) = TCSlib.Cryptography.EnsembleLemmas.padL k a := rfl\n",
   "theorem ctlPadLReader (k : ℕ) (a : List Bool) :\n    List.ofFn (TCSlib.Cryptography.padFin k a) = TCSlib.Cryptography.EnsembleLemmas.padL k a :=\n  TCSlib.Cryptography.EnsembleLemmas.ofFn_padFin_eq_padL k a\n"),
 'TCSlib.Cryptography.xorPerm': row("ctlXorPerm",
   "theorem ctlXorPerm {n : ℕ} (v y : Fin n → Bool) :\n    TCSlib.Cryptography.xorPerm v y = fun i => xor (y i) (v i) := rfl\n",
   "theorem ctlXorPermReader {n : ℕ} (v y : Fin n → Bool) :\n    TCSlib.Cryptography.xorPerm v y = fun i => xor (y i) (v i) :=\n  TCSlib.Cryptography.xorPerm_apply v y\n"),
 IH + '.rU': row("ctlRU",
   f"theorem ctlRU (w : List Bool) :\n    {IH}.rU w = Complexity.pairFstD (Complexity.pairFstD w) := rfl\n",
   f"theorem ctlRUReader {{k : ℕ}} (n : ℕ) (z ω s : List Bool) (i : Fin k) (x L : List Bool) :\n    {IH}.rU ({IH}.input n z ω s i x L) = List.replicate n true :=\n  {IH}.rU_input n z ω s i x L\n"),
 PK + '.indCodec': row("ctlPkIndCodec",
   f"open TCSlib.Cryptography.Games in\ntheorem ctlPkIndCodec (S : {PK}) (n : ℕ) :\n    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl\n",
   f"open TCSlib.Cryptography.Games in\ntheorem ctlPkIndCodecReader (S : {PK}) (n : ℕ) :\n    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := S.indCodec_eq_bitCodec n\n"),
 SK + '.indCodec': row("ctlSkIndCodec",
   f"open TCSlib.Cryptography.Games in\ntheorem ctlSkIndCodec (S : {SK}) (n : ℕ) :\n    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := rfl\n",
   f"open TCSlib.Cryptography.Games in\ntheorem ctlSkIndCodecReader (S : {SK}) (n : ℕ) :\n    S.indCodec n = bitCodec (S.inLens n) (S.outLens n) 1 := S.indCodec_eq_bitCodec n\n"),
 SK + '.splitHalf': row("ctlSplitHalf",
   f"theorem ctlSplitHalf {{n : ℕ}} (x : Fin (n + n) → Bool) :\n    ({SK}.splitHalf x).1 = fun i => x (Fin.castAdd n i) := rfl\n",
   f"theorem ctlSplitHalfReader {{n : ℕ}} (x : Fin (n + n) → Bool) :\n    ({SK}.splitHalf x).1 = fun i => x (Fin.castAdd n i) := {SK}.splitHalf_fst x\n"),
 CS + '.chRun': row("ctlChRun",
   f"theorem ctlChRun {{ins outs : Fin 2 → ℕ}} {{α : Type}} (g : (Fin (ins 1) → Bool) → List Bool) (a : α)\n    (s : Option (Fin (outs 1) → Bool)) : {CS}.chRun g (.pure a) s = (a, s) := rfl\n",
   f"theorem ctlChRunReader {{ins outs : Fin 2 → ℕ}} {{α : Type}} (g : (Fin (ins 1) → Bool) → List Bool) (a : α)\n    (s : Option (Fin (outs 1) → Bool)) : {CS}.chRun g (.pure a) s = (a, s) :=\n  {CS}.chRun_pure g a s\n"),
}
def assemble(label, module, rows, bodies, sealed):
    src = (f"import Lean\nimport {module}\n\nset_option maxHeartbeats 0\nset_option autoImplicit false\n"
           "set_option relaxedAutoImplicit false\n\n").encode()
    if sealed: src += bs.seal_command(label, rows, end=False)
    src += b"namespace DlControls\n\n"
    expect = []
    for name, target, negative, body in bodies:
        start = src.count(b"\n") + 1
        src += body.encode() + b"\n"
        expect.append(dict(control=name, target=target, negative=negative, start_line=start,
                           end_line=start + body.count('\n') - 1))
    src += b"end DlControls\n\n"
    if sealed: src += bs.seal_command(label, rows, end=True)
    return src, expect
out = Path(outdir); out.mkdir(parents=True, exist_ok=True); plan = []
# dl-consolidation review: controls only for a covering subset of the seal records: for each target of B
# (and each variant letter), the seal record with the fewest requests whose request set contains it.
recs = [json.load(open(p)) for p in sorted(Path(sealdir).glob('Seal?_*.json'))]
chosen = {}
for t in B:
    for letter in sorted({r['label'][4] for r in recs}):
        c = [r for r in recs if r['label'][4] == letter and t in {x['spelling'] for x in r['rows']}]
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
