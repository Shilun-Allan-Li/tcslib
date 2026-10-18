"""Build the MIG-0b round-2 landing unit (standard library only; python3 -I).

Usage: python3 -I build.py <worktree> <outdir>

Every block of the unit comes from one of four sources, recorded in <outdir>/manifest.json:
* `landed`: `TCSlib/Complexity/TuringMachine/Build/Contract.lean` of the worktree (the MIG-0a file
  as landed by PR #83), taken by declaration name;
* `r1`: the round-1 evidence (`audits/evidence/mig0b/Contract-mig0b-draft.lean.txt` from line 1100
  and `Contract-mig0b-adapters.lean.txt` from line 2664), taken by declaration name;
* `file:<path>`: a worktree source file (moves and full-file edits);
* `new`: `src/new.lean` (new text, keyed by `-- %%% key` lines).
Every edit is an exact replacement asserted to match the stated number of times (default one).
Every landed declaration must be taken exactly once or appear in LANDED_RETIRED; every round-1
declaration outside `MIG0bFit` must be taken once or appear in R1_RETIRED.
"""
import hashlib
import importlib.util
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('blocks', os.path.join(HERE, 'blocks.py'))
blocks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(blocks)

WT, OUT = sys.argv[1], sys.argv[2]
SRC = os.path.join(HERE, '..', 'src')
TM = 'TCSlib/Complexity/TuringMachine/'


def read(p):
    return open(os.path.join(WT, p), encoding='utf-8').read()


LANDED_PATH = TM + 'Build/Contract.lean'
landed_text = read(LANDED_PATH)
D = read('audits/evidence/mig0b/Contract-mig0b-draft.lean.txt').split('\n')
A = read('audits/evidence/mig0b/Contract-mig0b-adapters.lean.txt').split('\n')
assert len(D) == 2662 and len(A) == 3284, (len(D), len(A))  # 2661 / 3283 lines + final ''
R1_TEXTS = ['\n'.join(D[1099:]), '\n'.join(A[2663:])]

landed_decls = blocks.decls(landed_text)[0]
r1_decls = {}
for t in R1_TEXTS:
    for k, v in blocks.decls(t)[0].items():
        assert k not in r1_decls, k
        r1_decls[k] = v
file_decls = {}

NEW = {}
cur = None
for line in open(os.path.join(SRC, 'new.lean'), encoding='utf-8').read().split('\n'):
    if line.startswith('-- %%% '):
        cur = line[len('-- %%% '):].strip()
        NEW[cur] = []
    else:
        NEW[cur].append(line)
NEW = {k: '\n'.join(v).strip('\n') for k, v in NEW.items()}

manifest = []
used = {'landed': set(), 'r1': set(), 'new': set()}


def edit(text, edits, label):
    for e in edits:
        old, new = e[0], e[1]
        n = e[2] if len(e) > 2 else 1
        c = text.count(old)
        assert c == n, f'{label}: edit expects {n} match(es), found {c}: {old[:70]!r}'
        text = text.replace(old, new)
    return text


def take(src, name, edits=(), note=''):
    if src == 'landed':
        text = landed_decls[name]
    elif src == 'r1':
        text = r1_decls[name]
    else:
        path = src[len('file:'):]
        if path not in file_decls:
            file_decls[path] = blocks.decls(read(path))[0]
        text = file_decls[path][name]
    key = src if src in used else 'file'
    if key in used:
        assert name not in used[key], f'{src} {name} taken twice'
        used[key].add(name)
    out = edit(text, edits, f'{src} {name}')
    manifest.append({'name': name, 'source': src, 'edited': bool(edits), 'note': note,
                     'sha256_source': hashlib.sha256(text.encode()).hexdigest(),
                     'sha256_unit': hashlib.sha256(out.encode()).hexdigest()})
    return out


def new(key):
    used['new'].add(key)
    return NEW[key]


HEADER_RULE = '/-! ' + '═' * 96


def part(n, title, landing, imports, body, moved_from=None):
    import textwrap
    lines = [HEADER_RULE] + textwrap.wrap(f'Part {n}. ' + ' '.join(title.split()) + ' -/', 100,
                                          break_on_hyphens=False)
    lines.append(f'-- @landing {landing}')
    if moved_from:
        lines.append(f'-- @moved-from {moved_from}')
    imps, cur = [], '-- @imports'
    for m in imports:
        if len(cur) + 1 + len(m) > 100:
            imps.append(cur)
            cur = '-- @imports'
        cur += ' ' + m
    imps.append(cur)
    return '\n'.join(lines + imps) + '\n' + body.strip('\n') + '\n'


def join(*xs):
    return '\n\n'.join(x.strip('\n') for x in xs if x is not None) + '\n'


# ── Shared edits ─────────────────────────────────────────────────────────────────────────────

HULL_L = 'Finset.Icc_subset_Icc (min_le_left _ _) (le_max_left _ _)'
HULL_R = 'Finset.Icc_subset_Icc (min_le_right _ _) (le_max_right _ _)'
NE_LE = 'MultiTapeTM.runFrom_state_ne_none_of_le'

E_TRANS = [
    ('    · exact mem_hull_left (C₁.env i d hd hp u h j)',
     f'    · exact {HULL_L} (C₁.env i d hd hp u h j)'),
    ('      exact mem_hull_right (C₂.env _ _ hx (hlink i d hd hp) v (by omega) j)',
     f'      exact {HULL_R}\n        (C₂.env _ _ hx (hlink i d hd hp) v (by omega) j)'),
    ('endpoint need not be a first exit belongs to MIG-0b\'s segment layer.',
     'endpoint need not be a first exit belongs to the segment layer (`Turing.Segment.trans`).'),
]
E_SEQ = [
    ('      exact mem_hull_left (C₁.env i _ hd₁ hp u hle j)',
     f'      exact {HULL_L} (C₁.env i _ hd₁ hp u hle j)'),
    ('      exact mem_hull_right (C₂.env _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) j)',
     f'      exact {HULL_R}\n        (C₂.env _ _ hd₂ (hlink i _ hd₁ hp) v (by omega) j)'),
]
E_SEQ_TRAJ = [
    ('  · intro h\n    have h\' := runFrom_state_none_mono h hu\n    rw [h1, hx] at h\'\n'
     '    exact Option.some_ne_none _ h\'',
     f'  · refine {NE_LE} M₁ _ _ ?_ u hu\n    rw [h1, hx]\n    exact Option.some_ne_none _'),
]
E_LIVE = [
    ('  intro h\n  have h\' := runFrom_state_none_mono h hu.le\n  rw [C.run i d hd hp] at h\'\n'
     '  have hx := C.exit_mem i d hd hp\n  rw [h\'] at hx\n  exact C.cut i d hd hp u hu (h ▸ hx)',
     '  intro h\n  have hend : (M.runFrom d (C.time i d)).state ≠ none := by\n    intro h\'\n'
     '    have hx := C.exit_mem i d hd hp\n    rw [← C.run i d hd hp, h\'] at hx\n'
     '    exact C.cut i d hd hp u hu (h ▸ hx)\n'
     f'  exact {NE_LE} M d _ hend u hu.le h'),
]
E_BRANCH_TRAJ = [
    ('  · intro h\n    have h\' := runFrom_state_none_mono h hu\n    rw [h0] at h\'\n'
     '    rw [h\'] at hx\n    simp at hx',
     f'  · refine {NE_LE} M₀ _ _ ?_ u hu\n    rw [h0]\n    intro h\'\n    rw [h\'] at hx\n'
     '    simp at hx'),
]
E_BRANCH = [
    ('      exact mem_hull_left (C₀.env i _ hc hp u hle j)',
     f'      exact {HULL_L} (C₀.env i _ hc hp u hle j)'),
    ('        exact mem_hull_right (C₁.env _ _ hd₁ (h₁ i _ hc hp h) v (by omega) j)',
     f'        exact {HULL_R}\n          (C₁.env _ _ hd₁ (h₁ i _ hc hp h) v (by omega) j)'),
    ('        exact mem_hull_right (C₂.env _ _ hd₂ (h₂ i _ hc hp h\') v (by omega) j)',
     f'        exact {HULL_R}\n          (C₂.env _ _ hd₂ (h₂ i _ hc hp h\') v (by omega) j)'),
]
E_RC_RELEASE_LANDED = [  # Q14: the envelope through the pointwise release lockstep
    ('fresh state is left-tagged. The exit is the endpoint\'s state, the anchor, right-tagged. For the\n'
     'envelope, a head position up to the endpoint lies in the release machine\'s visited set, which\n'
     'is the source\'s (`Turing.seamReleaseTM_visitedByTapeHead`); so it is the source head at some\n'
     'time up to the endpoint, inside the source envelope. The visited-set theorem is used because\n'
     'the pointwise lemma is private in `Build/Seam`; its export, `seamReleaseTM_runFrom_pos`, is\n'
     'deferred to MIG-0b. -/',
     'fresh state is left-tagged. The exit is the endpoint\'s state, the anchor, right-tagged. For the\n'
     'envelope, the head vector at time `0` is the start\'s; at a positive time the release run is\n'
     'the source run, right-tagged (`Turing.seamReleaseTM_runFrom_pos`), so its heads are the\n'
     'source\'s, inside the source envelope. -/'),
    ('    change u ≤ C.time i (d.mapState fun _ => anchor) at hu\n'
     '    have hv := seamReleaseTM_visitedByTapeHead M anchor hc (C.time i (d.mapState fun _ => anchor)) j\n'
     '    rw [release_start hd] at hv\n'
     '    have hmem : ((seamReleaseTM M anchor).runFrom d u).workTapePos j ∈\n'
     '        (seamReleaseTM M anchor).visitedByTapeHead d (C.time i (d.mapState fun _ => anchor)) j :=\n'
     '      Finset.mem_image.mpr ⟨u, Finset.mem_range.mpr (by omega), rfl⟩\n'
     '    rw [hv] at hmem\n'
     '    obtain ⟨s, hs, hseq⟩ := Finset.mem_image.mp hmem\n'
     '    rw [← hseq]\n'
     '    exact C.env i _ hc hp s (Nat.lt_succ_iff.mp (Finset.mem_range.mp hs)) j',
     '    rcases Nat.eq_zero_or_pos u with rfl | hpos\n'
     '    · have h0 := C.env i _ hc hp 0 (Nat.zero_le _) j\n'
     '      rw [MultiTapeTM.runFrom_zero] at h0 ⊢\n'
     '      exact h0\n'
     '    · have H := seamReleaseTM_runFrom_pos M anchor _ hc u hpos\n'
     '      rw [release_start hd] at H\n'
     '      rw [H]\n'
     '      exact C.env i _ hc hp u hu j'),
]
E_UNSELECTED = [
    ('`Build/Embed` with MIG-0b\'s layering split (backlog MIG-0).',
     '`Build/Embed` from `Build/Contract.lean` at MIG-0b\'s layering split.'),
    ('It moves to\n`Build/Embed`', 'It moved to\n`Build/Embed`'),
    ('theorem _root_.Turing.embedEmitCfg_unselected {m : ℕ} {S : Type}',
     'theorem embedEmitCfg_unselected {m : ℕ} {S : Type*}'),
]
E_SELECT_DEF = [('def _root_.Turing.Cfg.select {m : ℕ} {S : Type}', 'def Cfg.select {m : ℕ} {S : Type*}')]
E_SELECT_THM = [
    ('**Proof sketch.** Compare field by field. The state and the input position are the\n'
     'selection\'s, which are `d`\'s. A selected tape or head is the selection\'s, which is `d`\'s, by the\n'
     'public selected-field lemmas. An unselected tape or head is the frame, which is `d`\'s, by the\n'
     'public frame lemma at time `0` for a trivial machine on `Unit` (the transport\'s tape fields do not\n'
     'depend on the state type). The output is `d`\'s followed by the selection\'s empty output. -/',
     '**Proof sketch.** The R1 reconstruction lemma (`Turing.embedEmitCfg_eq`) at `d`\'s own tapes,\n'
     'heads and output: the selection keeps the state, the input position and the selected tapes and\n'
     'heads, its empty output follows `d`\'s, and off the selection the frame is `d`\'s own. -/'),
    ('theorem _root_.Turing.embedEmitCfg_select {m : ℕ} {S : Type}',
     'theorem embedEmitCfg_select {m : ℕ} {S : Type*}'),
    ('    embedEmitCfg σ d.workTapes d.workTapePos d.output (d.select σ) = d := by\n',
     '    embedEmitCfg σ d.workTapes d.workTapePos d.output (d.select σ) = d :=\n'
     '  embedEmitCfg_eq σ _ _ _ _ d rfl rfl (List.append_nil _) (fun _ => ⟨rfl, rfl⟩)\n'
     '    (fun _ _ => ⟨rfl, rfl⟩)\n'
     '-- %%CUT%%\n'),
]


def cut_after_marker(text):
    """Drop everything after a `-- %%CUT%%` line (used to replace a whole proof)."""
    i = text.find('\n-- %%CUT%%\n')
    return text if i < 0 else text[:i]


E_R1_SEG_LIVE = [
    ('  · have h\' := Contract.runFrom_state_none_mono hm hu.le\n    rw [h.1] at h\'\n'
     '    exact hb h\'',
     f'  · exact {NE_LE} M a t (by rw [h.1]; exact hb) u hu.le hm'),
    ('(`runFrom_state_none_mono`)', '(`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`)'),
]
E_R1_TOROUND = [
    ('    | none =>\n      have h\' := Contract.runFrom_state_none_mono hs hut.le\n'
     '      rw [C.run i d hd hp, C.exit_eq i d hd hp] at h\'\n'
     '      exact absurd h\' (Option.some_ne_none _)',
     f'    | none =>\n      refine absurd hs ({NE_LE} M d _ ?_ u hut.le)\n'
     '      rw [C.run i d hd hp, C.exit_eq i d hd hp]\n      exact Option.some_ne_none _'),
    ('(`runFrom_state_none_mono`), so a halt before the time would make the endpoint\'s state `none`,\n'
     'not the anchor. -/',
     '(`Turing.MultiTapeTM.runFrom_state_ne_none_of_le`), so a halt before the time would make\n'
     'the endpoint\'s state `none`, not the anchor. -/'),
]
E_R1_DONE_WITNESS = [
    ('**Proof sketch.** The round layer gives the public theorem\'s round hypothesis\n'
     '(`Turing.MIG0bFit.counterLoop_hround_of_rounds`); its conclusion is the segment, and the live\n'
     'endpoint adds liveness (`Turing.Segment.live`). -/',
     '**Proof sketch.** The round cut, read in the rows\' form (`Turing.Round.cut_some`), gives the\n'
     'public theorem\'s round hypothesis; its conclusion is the segment, and the live endpoint adds\n'
     'liveness (`Turing.Segment.live`). -/'),
    ('  obtain ⟨hrun, hcut, hctr, hbody⟩ := counterLoopTMVia_run_done e M a exit τ c w ct cp hw d hd\n'
     '    (MIG0bFit.counterLoop_hround_of_rounds M a exit τ c d hround) _ rfl\n',
     '  have hr : ∀ r < d,\n'
     '      (roundOrbit M τ c r).state = some a ∧ 0 < τ (roundOrbit M τ c r) ∧\n'
     '      (∀ u, 0 < u → u < τ (roundOrbit M τ c r) →\n'
     '        ∃ s, (M.runFrom (roundOrbit M τ c r) u).state = some s ∧ s ≠ a ∧ exit ≠ some s) ∧\n'
     '      (roundOrbit M τ c (r + 1)).state = some a := by\n'
     '    intro r hr\n'
     '    obtain ⟨hR, hret⟩ := hround r hr\n'
     '    refine ⟨hR.1, hR.2.1, fun u hu hut => ?_, hret⟩\n'
     '    obtain ⟨s, hs, hsa, hsE⟩ := hR.cut_some u hu hut\n'
     '    exact ⟨s, hs, hsa, fun h\' => hsE (h\' ▸ rfl)⟩\n'
     '  obtain ⟨hrun, hcut, hctr, hbody⟩ :=\n'
     '    counterLoopTMVia_run_done e M a exit τ c w ct cp hw d hd hr _ rfl\n'),
]
E_R1_RC_RELEASE = [
    ('/-- **The round release** (design §16a item 2, with item 5\'s export): a fresh start state\n'
     'executes the anchor\'s first step, so a round becomes an ordinary contract whose exits are the\n'
     'right-tagged anchor and escapes, at the same time and with the same envelope. Return and escape\n'
     'then reach a seam or the phase host as two live exits (`Turing.Contract.branch`,\n'
     '`Turing.Contract.inPhase`).\n',
     '/-- **The round release** (design §16a item 2, with item 5\'s export): a fresh start state\n'
     'executes the anchor\'s first step, so a round becomes an ordinary contract whose exits are the\n'
     'right-tagged images of the anchor and of the escape set, at the same time and with the same\n'
     'envelope. The escape set is arbitrary: it may contain `none` (a round that halts still ends\n'
     'halted, since the tag keeps `none`), several states, or the anchor itself. **Only for a single\n'
     'live escape distinct from the anchor**, `escape = {some e}` with `e ≠ anchor`, are the exits two\n'
     'distinct live states, `some (Sum.inr anchor)` and `some (Sum.inr e)`, the shape of\n'
     '`Turing.Contract.branch`\'s first phase. Routing through the phase host\n'
     '(`Turing.Contract.inPhase`) needs in general that `none` is not an exit and the redirect\n'
     'conditions.\n'),
]
E_R1_AR = None  # the whole docstring is replaced, below
E_R1_WORK = None  # replaced by the generalized statement in `new`
E_R1_LOCKSTEP = [
    ('hull over the source run. -/',
     'hull over the source run.\n\n'
     'The target entry `entry\'` is a free parameter: no premise relates it to the encoding. A\n'
     'useful instance needs every source configuration at `entry` to be encoded at `entry\'`\n'
     '(`Turing.Contract.lockstep_admissible`; for a state-renaming encoding,\n'
     '`Turing.Contract.lockstep_admissible_map`), and otherwise the contract may have no admissible\n'
     'start. -/'),
]
E_R1_ROUNDORBIT = [
    ('steps. It is `CounterLoop`\'s `counterLoopOrbit` (definitionally; see the adapter probe), stated in\n'
     'the core so that round iteration needs no counter. -/',
     'steps, stated in the core so that round iteration needs no counter. `CounterLoop`\'s\n'
     '`Turing.counterLoopOrbit` is an abbreviation of it. -/'),
]
E_R1_R1EQ = [
    ('theorem embedEmitCfg_eq {m : ℕ} {S : Type}', 'theorem embedEmitCfg_eq {m : ℕ} {S : Type*}'),
    ('into that frame. It moves to `Build/Embed` at the layering split and replaces\n'
     '`OracleSim.oracleBankCfg_eq`, `CodeSimulator.canonEmbedEq`, `Primitives.emitterP2_frame` and the\n'
     'local `hframe` of `Loop.emCall_exit_fixed` (see the fit tests below).',
     'into that frame. At their migrations it replaces `OracleSim.oracleBankCfg_eq`,\n'
     '`CodeSimulator.canonEmbedEq`, `Primitives.emitterP2_frame` and the local `hframe` of\n'
     '`Loop.emCall_exit_fixed` (the MIG-0b fit tests derive each in one term).'),
]
E_R1_MAPSTATE_EQ = [('theorem embedEmitCfg_mapState_eq {m : ℕ} {S H : Type}',
                      'theorem embedEmitCfg_mapState_eq {m : ℕ} {S H : Type*}')]
E_R1_OFWORDS = [
    ('theorem embedEmitCfg_ofWords_eq {m : ℕ} {S : Type}',
     'theorem embedEmitCfg_ofWords_eq {m : ℕ} {S : Type*}'),
    ('the frame\'s. This is the shape of `CodeSimulator.canonEmbedWords` and `CertShell.cert_embed_words`;\n'
     'it lives with `Turing.Cfg.ofWords` (`Build/Convention`) above `Build/Embed`.',
     'the frame\'s. This is the shape of `CodeSimulator.canonEmbedWords` and `CertShell.cert_embed_words`\n'
     '(`Build/Embed` imports `Build/Convention`, where `Turing.Cfg.ofWords` lives, for it).'),
]
E_R1_LOCKSTEP_DEF = [
    ('meets no target exit. Alphabet reduction is the case `cost = 3(|Γ| + 1) + 2`; a lockstep\n'
     'decoration is the case `cost = 1`. -/',
     'meets no target exit. Alphabet reduction ([AB09, Claim 1.5]) is the case\n'
     '`cost = 3(|Γ| + 1) + 2`; a lockstep decoration is the case `cost = 1`. Neither a positive cost\n'
     'nor an injective encoding is required. -/'),
]
E_R1_MAPSTATE = []

# ── Seam: the full-file edits ────────────────────────────────────────────────────────────────

seam_text = read(TM + 'Build/Seam.lean')
SEAM_PRIV_RELEASE_START = '/-- The fresh state executes the anchor action without a dispatch step. -/\n'
SEAM_PRIV_RELEASE_END = ('    exact MultiTapeTM.runFrom_comm_of_step (Cfg.mapState Sum.inr)\n'
                         '      (seamRelease_step_right M anchor) _ t\n')


def seam_full():
    t = seam_text
    i = t.index('\n/-!\n# Machine-construction library: seam composition (R2)')
    body = t[i + 1:]
    s = body.index(SEAM_PRIV_RELEASE_START)
    e = body.index(SEAM_PRIV_RELEASE_END) + len(SEAM_PRIV_RELEASE_END)
    assert body.count(SEAM_PRIV_RELEASE_START) == 1 and body.count(SEAM_PRIV_RELEASE_END) == 1
    body = body[:s] + new('seam_promoted') + '\n' + body[e:]
    old_right_head = ('/-- After the one-step dispatch, the entire right trajectory agrees.\n'
                      '**Proof sketch.** Split the run at the dispatch, use left lockstep and\n'
                      'the exit equation, then iterate the unconditional right-step identity. -/\n'
                      'private lemma seamComp_right {Symbol : Type*} {x : List Symbol} '
                      '[DecidableEq S₁]\n')
    body = edit(body, [
        (old_right_head, new('seam_right') + '\n'),
        ('seamComp_right M₁ exit M₂ entry', 'seamCompTM_runFrom_right M₁ exit M₂ entry', 3),
        ('seamRelease_run_pos M anchor c hc', 'seamReleaseTM_runFrom_pos M anchor c hc', 3),
        ('* `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM₂_run_ofCfg` — the left\n'
         '  prefix of a seam under a strict exit cut, and the two-exit composition\n'
         '  (§12.8, R8.8; the latter a statement).\n',
         '* `Turing.seamCompTM_runFrom_left`, `Turing.seamCompTM₂_run_ofCfg` — the left\n'
         '  prefix of a seam under a strict exit cut, and the two-exit composition\n'
         '  (§12.8, R8.8; the latter a statement).\n'
         '* `Turing.seamCompTM_runFrom_right` — the right segment after the dispatch, at any\n'
         '  offset (promoted from the private `seamComp_right` at MIG-0b; set-valued exits need it).\n'
         '* `Turing.seamReleaseTM_step_fresh`, `Turing.seamReleaseTM_step_inr`,\n'
         '  `Turing.seamReleaseTM_runFrom_pos` — the release adapter\'s steps and its pointwise\n'
         '  lockstep at every positive time (promoted from the private `seamRelease_*` lemmas at\n'
         '  MIG-0b, design §16a item 5).\n'),
    ], 'Seam full-file edit')
    assert 'seamRelease_run_pos' not in body.replace('`seamRelease_run_pos`', '')
    assert 'seamComp_right' not in body.replace('`seamComp_right`', '')
    return body


# ── CounterLoop: the full-file edits ─────────────────────────────────────────────────────────

cl_text = read(TM + 'Build/CounterLoop.lean')


def cl_full():
    t = cl_text
    i = t.index('\n/-!\n# Machine-construction library: counter-driven loops (§12.7)')
    body = t[i + 1:]
    body = edit(body, [
        ('/-- The body configurations at the starts of successive rounds: round `r`\n'
         'starts from `counterLoopOrbit M τ c r`, and a round from `c` lasts `τ c`\n'
         'steps. -/\n'
         'def counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol} (M : MultiTapeTM k Symbol S)\n'
         '    (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) : Cfg k Symbol S x :=\n'
         '  (fun c => M.runFrom c (τ c))^[r] c\n',
         '/-- The body configurations at the starts of successive rounds: round `r`\n'
         'starts from `counterLoopOrbit M τ c r`, and a round from `c` lasts `τ c`\n'
         'steps. Since MIG-0b it is an abbreviation of the core\'s round orbit `Turing.roundOrbit`\n'
         '(`Build/Contract/Basic`), the iterate `(fun c => M.runFrom c (τ c))^[r] c`; a proof that\n'
         'unfolds it unfolds `Turing.roundOrbit` too. -/\n'
         'abbrev counterLoopOrbit {k : ℕ} {Symbol S : Type} {x : List Symbol}\n'
         '    (M : MultiTapeTM k Symbol S) (τ : Cfg k Symbol S x → ℕ) (c : Cfg k Symbol S x) (r : ℕ) :\n'
         '    Cfg k Symbol S x :=\n'
         '  roundOrbit M τ c r\n'),
        ('by simp [counter_layout, counterLoopOrbit]⟩',
         'by simp [counter_layout, counterLoopOrbit, roundOrbit]⟩'),
        ('* `Turing.expandTM_run_ofCfg` — the expansion writes its pattern once per\n'
         '  counter unit, contiguously, at exact time (modulo the advancing writer, §12.8).\n',
         '* `Turing.expandTM_run_ofCfg` — the expansion writes its pattern once per\n'
         '  counter unit, contiguously, at exact time (modulo the advancing writer, §12.8).\n'
         '* MIG-0b, over the round layer of `Build/Contract/Basic`:\n'
         '  `Turing.counterLoopTMVia_done_witness`, `Turing.counterLoopTMVia_escape_witness` (the host\n'
         '  segments with the shared round-and-offset witness) and their `_segment` corollaries;\n'
         '  `Turing.counterLoopCfg_body` (the host layout as an R1 reconstruction); and the\n'
         '  contract-level compositions `Turing.RoundContract.counterLoopDone` and\n'
         '  `Turing.RoundContract.counterLoopEscape`, with their `_traj` joint trajectories.\n'),
    ], 'CounterLoop full-file edit')
    return body


# ── The parts ────────────────────────────────────────────────────────────────────────────────

M_FIN = 'TCSlib.Complexity.TuringMachine.Finite'
M_SR = 'TCSlib.Complexity.TuringMachine.StateRenaming'
M_SIM = 'TCSlib.Complexity.TuringMachine.Simulation'
M_EMB = 'TCSlib.Complexity.TuringMachine.Build.Embed'
M_CONV = 'TCSlib.Complexity.TuringMachine.Build.Convention'
M_SEAM = 'TCSlib.Complexity.TuringMachine.Build.Seam'
M_CAT = 'TCSlib.Complexity.TuringMachine.Build.Catalog'
M_CL = 'TCSlib.Complexity.TuringMachine.Build.CounterLoop'
M_AR = 'TCSlib.Complexity.TuringMachine.Robustness.AlphabetReduction'
M_LIFT = 'TCSlib.Complexity.TuringMachine.SymbolLift'
M_SCAN = 'TCSlib.Complexity.TuringMachine.Build.Scan'
C = 'TCSlib.Complexity.TuringMachine.Build.Contract'
M_BASIC, M_CSEAM, M_CEMB, M_CCAT, M_CLIFT = (C + '.Basic', C + '.Seam', C + '.Embed',
                                              C + '.Catalog', C + '.Lift')
CAT = 'file:' + TM + 'Build/Catalog.lean'
EMB = 'file:' + TM + 'Build/Embed.lean'

parts = []

parts.append(part(1, '**Appended to `Finite.lean`** (moved down from `Build/Catalog.lean:386`, '
                  'verbatim). The core needs it\nfor `Turing.Contract.spaceUsedByTape_le`. '
                  '`Finite.lean` is the home of raw-layer additions, so that the vendored\n'
                  '`Deterministic.lean` stays byte-comparable with upstream.',
                  M_FIN, [M_FIN],
                  join('namespace Turing',
                       take(CAT, 'Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc',
                            note='moved verbatim from Build/Catalog'),
                       'end Turing'),
                  moved_from=M_CAT))

parts.append(part(2, '**Appended to `Finite.lean`** (new): the time-derived head envelope, the '
                  'round-1 export\ngeneralized to any alphabet and state type.',
                  M_FIN, [M_FIN], new('finite_new')))
manifest.append({'name': 'Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc', 'source': 'new',
                 'edited': True, 'note': 'round-1 statement generalized from Type to Type*'})
used['r1'].add('Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc')

parts.append(part(3, '**Appended to `StateRenaming.lean`** (moved down from '
                  '`Build/Embed.lean:1010`, verbatim), which\nthen imports `Simulation` (for '
                  '`AgreeOn`); `Simulation` does not import `StateRenaming`.',
                  M_SR, [M_SR, M_SIM],
                  join('namespace Turing', 'variable {Symbol : Type*}',
                       '/-! ## Guarded state transport (moved from `Build/Embed` at MIG-0b\'s '
                       'layering split) -/',
                       take(EMB, 'Turing.MultiTapeTM.runFrom_mapState_of_agreeOn',
                            note='moved verbatim from Build/Embed'),
                       'end Turing'),
                  moved_from=M_EMB))

parts.append(part(4, '**Appended to `Build/Embed.lean`**, which then imports `Build/Convention`. '
                  'MIG-0a\'s two Embed\nexports (moved from `Build/Contract.lean`) and the R1 '
                  'reconstruction lemma with its corollaries.',
                  M_EMB, [M_EMB, M_CONV],
                  join(new('embed_head'),
                       take('landed', 'Turing.embedEmitCfg_unselected', E_UNSELECTED),
                       take('landed', 'Turing.Cfg.select', E_SELECT_DEF),
                       take('r1', 'Turing.embedEmitCfg_eq', E_R1_R1EQ),
                       take('r1', 'Turing.embedEmitCfg_mapState_eq', E_R1_MAPSTATE_EQ),
                       take('r1', 'Turing.embedEmitCfg_ofWords_eq', E_R1_OFWORDS),
                       cut_after_marker(take('landed', 'Turing.embedEmitCfg_select', E_SELECT_THM,
                                             note='proof re-derived from embedEmitCfg_eq')),
                       'end Turing')))

parts.append(part(5, '**`Build/Seam.lean`, the whole file as edited** (it replaces the existing '
                  'file; no existing\nmodule of any check imports the old one). Edits: the private '
                  '`seamComp_right` and `seamRelease_*`\nlemmas promoted, with their universes and '
                  'proofs; their call sites renamed; the module docstring.',
                  M_SEAM, [M_CONV, M_SR, M_EMB], seam_full()))

basic = join(
    new('basic_head'),
    take('landed', 'Turing.Contract'),
    'namespace Contract',
    'section Derived',
    'variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}\n'
    '  {x : List Γ}',
    take('landed', 'Turing.Contract.within'),
    take('landed', 'Turing.Contract.spaceUsedByTape_le'),
    take('landed', 'Turing.Contract.Positive'),
    take('landed', 'Turing.Contract.mem_Icc_of_abs_le'),
    'end Derived',
    take('landed', 'Turing.Contract.trans', E_TRANS),
    take('landed', 'Turing.Contract.live', E_LIVE),
    'end Contract',
    '/-! ## Frames: the derived layer (user decision, 2026-10-12)\n\n'
    'A contract\'s endpoint already states its frame (`{ d with … }`). The predicates below name the\n'
    'frame for composition proofs: a *footprint* per tape, `Turing.Cfg.SameOutside`, its `.keep`\n'
    'lemmas, and `Turing.Contract.Frames`. They are derived properties, not fields. The layer is\n'
    '[AFM26]\'s framing (`SameOn` and the `.keep` lemmas of `Lang/Regions.lean`), adapted from memory\n'
    'cells to the cells of each work tape (design adaptation). -/',
    take('landed', 'Turing.Cfg.SameOutside'),
    take('landed', 'Turing.Cfg.SameOutside.trans'),
    take('landed', 'Turing.Cfg.SameOutside.mapState'),
    take('landed', 'Turing.Cfg.SameOutside.keep_word'),
    take('landed', 'Turing.Cfg.SameOutside.keep_blank'),
    'namespace Contract',
    'variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}\n'
    '  {x : List Γ}',
    take('landed', 'Turing.Contract.Frames'),
    take('landed', 'Turing.Contract.frames_iff'),
    'end Contract',
    '/-! ## Returning contracts\n\nTheir release adapter is in `Build/Contract/Seam`. -/',
    take('landed', 'Turing.ReturnContract'),
    new('basic_seg_doc'),
    take('r1', 'Turing.HeadBox'),
    take('r1', 'Turing.Segment'),
    'namespace Segment',
    'variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}\n'
    '  {P : (Fin k → ℤ) → Prop}',
    *[take('r1', 'Turing.Segment.' + n) for n in
      ['zero', 'one', 'trans', 'mono', 'and', 'take', 'drop', 'time_eq', 'cons']],
    take('r1', 'Turing.Segment.live', E_R1_SEG_LIVE),
    'end Segment',
    take('r1', 'Turing.SafeSegment'),
    take('r1', 'Turing.safeSegment_iff'),
    'namespace SafeSegment',
    'variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {F : Set (Option S)}\n'
    '  {P : (Fin k → ℤ) → Prop}',
    *[take('r1', 'Turing.SafeSegment.' + n) for n in ['zero', 'trans', 'mono', 'endpoint_not_mem']],
    'end SafeSegment',
    'namespace Contract',
    'variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}\n'
    '  {x : List Γ}',
    take('r1', 'Turing.Contract.segment'),
    take('r1', 'Turing.Contract.ofSegment'),
    take('r1', 'Turing.Contract.time_envelope'),
    'end Contract',
    new('basic_round_doc'),
    take('r1', 'Turing.roundStop'),
    take('r1', 'Turing.not_mem_roundStop'),
    take('r1', 'Turing.Round'),
    'namespace Round',
    'variable {S : Type} {x : List Γ} {M : MultiTapeTM k Γ S} {a : S} {E : Set (Option S)}\n'
    '  {P : (Fin k → ℤ) → Prop}',
    *[take('r1', 'Turing.Round.' + n) for n in ['segment', 'cut_some', 'of_cut', 'time_box']],
    'end Round',
    take('r1', 'Turing.roundOrbit', E_R1_ROUNDORBIT),
    take('r1', 'Turing.roundOrbit_succ'),
    take('r1', 'Turing.Round.iterate'),
    take('r1', 'Turing.RoundContract'),
    'namespace RoundContract',
    'variable {S : Type} {M : MultiTapeTM k Γ S} {anchor : S} {escape : Set (Option S)} {ι : Type}\n'
    '  {x : List Γ}',
    *[take('r1', 'Turing.RoundContract.' + n) for n in ['round', 'returning', 'escaping']],
    'end RoundContract',
    take('r1', 'Turing.ReturnContract.toRound', E_R1_TOROUND),
    new('basic_hull_doc'),
    'namespace RoundContract',
    'variable {S : Type} {M : MultiTapeTM k Γ S} {a : S} {E : Set (Option S)} {ι : Type}\n'
    '  {x : List Γ}',
    *[take('r1', 'Turing.RoundContract.' + n) for n in
      ['hullLo', 'hullHi', 'orbit_anchor', 'orbit_round', 'orbit_start']],
    'end RoundContract',
    take('r1', 'Turing.headBox_lastCases'),
    new('basic_traj_doc'),
    'namespace Contract',
    take('r1', 'Turing.Contract.Traj'),
    'section TrajBasic',
    'variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}\n'
    '  {x : List Γ}',
    *[take('r1', 'Turing.Contract.' + n) for n in
      ['traj_env', 'Traj.mono', 'Traj.and', 'Traj.segment', 'Traj.trans', 'Frames.trans']],
    'end TrajBasic',
    'end Contract',
    new('basic_sanity_doc'),
    'namespace Contract',
    'section Sanity',
    'variable {S : Type} {M : MultiTapeTM k Γ S} {entry : S} {exits : Set (Option S)} {ι : Type}\n'
    '  {x : List Γ}',
    *[take('r1', 'Turing.Contract.' + n) for n in
      ['time_eq_zero_iff', 'positive_of_not_mem', 'not_mem_of_positive', 'trans_positive']],
    'end Sanity',
    'end Contract',
    new('basic_transport_doc'),
    'namespace Contract',
    take('r1', 'Turing.Contract.mapState_traj'),
    take('r1', 'Turing.Contract.mapState'),
    'end Contract',
    take('r1', 'Turing.Lockstep', E_R1_LOCKSTEP_DEF),
    'namespace Lockstep',
    'variable {k\' : ℕ} {Γ\' S S\' : Type} {x : List Γ} {x\' : List Γ\'} {M : MultiTapeTM k Γ S}\n'
    '  {N : MultiTapeTM k\' Γ\' S\'} {enc : Cfg k Γ S x → Cfg k\' Γ\' S\' x\'} {cost : Cfg k Γ S x → ℕ}\n'
    '  {X : Set (Option S)} {X\' : Set (Option S\')}',
    *[take('r1', 'Turing.Lockstep.' + n) for n in ['runFrom', 'cut', 'locate']],
    'end Lockstep',
    take('r1', 'Turing.Contract.lockstep', E_R1_LOCKSTEP),
    new('lockstep_admissible'),
    'end Turing')
parts.append(part(6, '**`Build/Contract/Basic.lean`** (new): the core. MIG-0a\'s core, moved from '
                  '`Build/Contract.lean`,\nand MIG-0b\'s layers. Imports only the machine core.',
                  M_BASIC, ['Mathlib.Tactic.Linarith', M_SIM, M_SR], basic))

ar_doc_old = r1_decls['Turing.FinTM.exists_alphabetReduction_lockstep']
ar_doc_end = ar_doc_old.index('theorem FinTM.exists_alphabetReduction_lockstep')
E_R1_AR = [(ar_doc_old[:ar_doc_end], new('ar_lockstep_doc') + '\n')]
parts.append(part(7, '**Appended to `Robustness/AlphabetReduction.lean`**, which then imports the '
                  'core. The\nalphabet-reduction adapter; its lockstep existence is the one '
                  '`sorry` (RS-5).',
                  M_AR, [M_AR, M_BASIC],
                  join(new('ar_head'),
                       take('r1', 'Turing.FinTM.exists_alphabetReduction_lockstep', E_R1_AR),
                       take('r1', 'Turing.FinTM.alphabetReduction_contract'),
                       'end Turing')))

cseam = join(
    new('cseam_head'),
    'namespace Contract',
    'section Compose',
    take('landed', 'Turing.Contract.mapState_state'),
    take('landed', 'Turing.Contract.mapState_const_inl'),
    take('landed', 'Turing.Contract.seq_traj', E_SEQ_TRAJ),
    take('landed', 'Turing.Contract.seq', E_SEQ),
    take('landed', 'Turing.Cfg.bindState'),
    take('landed', 'Turing.Contract.inPhase_traj'),
    take('landed', 'Turing.Contract.inPhase'),
    'end Compose',
    '/-! ## The two-way branch -/',
    take('landed', 'Turing.Contract.mapState_const_inl_inl'),
    take('landed', 'Turing.Contract.branch_traj', E_BRANCH_TRAJ),
    take('landed', 'Turing.Contract.branch', E_BRANCH),
    'end Contract',
    '/-! ## The release adapter -/',
    take('landed', 'Turing.release_start'),
    take('landed', 'Turing.ReturnContract.release', E_RC_RELEASE_LANDED),
    take('r1', 'Turing.RoundContract.release', E_R1_RC_RELEASE),
    '/-! ## Joint trajectories, frames and positivity of the seam compositions (MIG-0b) -/',
    'namespace Contract',
    *[take('r1', 'Turing.Contract.' + n) for n in
      ['Traj.seq', 'Frames.seq', 'Traj.inPhase', 'Traj.branch', 'seq_positive',
       'inPhase_positive', 'branch_positive']],
    'end Contract',
    take('r1', 'Turing.ReturnContract.release_positive'),
    take('r1', 'Turing.RoundContract.release_positive'),
    'end Turing')
parts.append(part(8, '**`Build/Contract/Seam.lean`** (new): the seam, phase-host and release '
                  'compositions.', M_CSEAM, [M_BASIC, M_SEAM], cseam))

parts.append(part(9, '**`Build/Contract/Embed.lean`** (new): transport along the R1 embedding.',
                  M_CEMB, [M_BASIC, M_EMB],
                  join(new('cembed_head'), 'namespace Contract',
                       take('landed', 'Turing.Contract.embed'),
                       take('r1', 'Turing.Contract.Traj.embed'),
                       take('r1', 'Turing.Contract.embed_positive'),
                       'end Contract', 'end Turing')))

parts.append(part(10, '**`Build/Contract/Catalog.lean`** (new): the routine instance.',
                  M_CCAT, [M_BASIC, M_CAT],
                  join(new('ccat_head'),
                       take('landed', 'Turing.clearTM_contract'),
                       take('landed', 'Turing.clearTM_contract_frames'),
                       take('r1', 'Turing.clearTM_contract_traj'),
                       'end Turing')))

parts.append(part(11, '**`Build/Contract/Lift.lean`** (new): the symbol lift.',
                  M_CLIFT, [M_BASIC, M_LIFT],
                  join(new('clift_head'), take('r1', 'Turing.Contract.liftSymbols'),
                       'end Turing')))

cl_add = join(
    new('cl_head'),
    take('r1', 'Turing.counterLoopTMVia_done_witness', E_R1_DONE_WITNESS),
    take('r1', 'Turing.counterLoopTMVia_done_segment'),
    take('r1', 'Turing.counterLoopTMVia_escape_witness'),
    take('r1', 'Turing.counterLoopTMVia_escape_segment'),
    take('r1', 'Turing.counterLoopBody'),
    take('r1', 'Turing.counterLoopCfg_body'),
    take('r1', 'Turing.counterValue'),
    take('r1', 'Turing.RoundContract.counterLoopDone'),
    take('r1', 'Turing.RoundContract.counterLoopEscape'),
    take('r1', 'Turing.RoundContract.counterLoopDone_traj'),
    take('r1', 'Turing.RoundContract.counterLoopEscape_traj'),
    'end Turing')
parts.append(part(12, '**`Build/CounterLoop.lean`, the whole file as edited** (it replaces the '
                  'existing file). Edits:\nit imports the core; `counterLoopOrbit` becomes an '
                  'abbreviation of `roundOrbit` (Q11), with the\none in-file proof that unfolds it '
                  'updated; the module docstring; and the counter loop over the\nround layer, '
                  'appended.',
                  M_CL, ['Mathlib.Data.Nat.Digits.Defs', 'Mathlib.Logic.Equiv.Bool', M_CAT,
                         M_SCAN, M_LIFT, M_BASIC],
                  join(cl_full(), cl_add)))

parts.append(part(13, '**`Build/Contract.lean`, replaced by the facade.**', C,
                  [M_BASIC, M_CSEAM, M_CEMB, M_CCAT, M_CLIFT], new('facade')))

# ── Bookkeeping assertions ───────────────────────────────────────────────────────────────────

LANDED_RETIRED = {
    'Turing.Contract.mem_hull_left': 'deleted (finding 1): consumers cite Finset.Icc_subset_Icc',
    'Turing.Contract.mem_hull_right': 'deleted (finding 1): consumers cite Finset.Icc_subset_Icc',
    'Turing.Contract.runFrom_state_none_mono':
        'deleted (finding 1): consumers cite MultiTapeTM.runFrom_state_ne_none_of_le (Finite)',
    'Turing.seamCompTM_runFrom_right':
        'replaced by the promoted polymorphic seamComp_right of Build/Seam (same name; '
        'the landed Type statement is an instance, checked in the fit file)',
}
R1_RETIRED = {
    'Turing.seamReleaseTM_runFrom_pos': 'dropped (finding 2): replaced by the promoted '
                                        'polymorphic Build/Seam lemma of the same name',
    'Turing.counterLoopOrbit_eq_roundOrbit': 'dropped (Q11): counterLoopOrbit is an abbreviation; '
                                             'kept as an `example` in the fit file',
}
missing_landed = set(landed_decls) - used['landed'] - set(LANDED_RETIRED)
assert not missing_landed, missing_landed
assert not (used['landed'] & set(LANDED_RETIRED))
r1_landable = {n for n in r1_decls if '.MIG0bFit.' not in n}
missing_r1 = r1_landable - used['r1'] - set(R1_RETIRED)
assert not missing_r1, missing_r1
assert not (used['r1'] & set(R1_RETIRED)), used['r1'] & set(R1_RETIRED)
assert {k for k in set(NEW) - used['new'] if not k.startswith('fit_')} <= {'lift_section'}

unit_head = '''/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/

/-!
# MIG-0b, round 2: the landing unit

**Not a module and not elaborated as one file.** This is the landing form of MIG-0b (design §16a):
thirteen parts, each introduced by a rule line, a `-- @landing <Module>` line, an optional
`-- @moved-from <Module>` line and `-- @imports …` lines. Each part becomes, or is appended to,
its landing module: the copyright block, the imports its `-- @imports` lines list, the standard
options, and the part verbatim. A part that lists its own landing module among its imports is
**appended** to that existing module; a part for an existing module that does not is the **whole
edited file**; the others are new modules. A `-- @moved-from` part holds declarations moved
verbatim from that module, whose old copies the landing deletes.

Each part is elaborated in exactly its own import closure by `cutcheck2.py` (the method of
`audits/evidence/stage2-gate/scripts/cutcheck.py`, extended to closures through existing modules,
whole-file parts and moves). The unit holds no fit test: the fit tests are a separate evidence
file that elaborates over all the parts. The unit was generated by `build.py` from the landed
`Build/Contract.lean` (PR #83, at campaign commit `385d6e5a`), the round-1 evidence and the
worktree sources, with every edit an asserted replacement; `manifest.json` gives each block's
source.
-/
'''
unit = unit_head + '\n' + '\n'.join(parts)
assert 'MIG0bFit' not in unit, 'the fit namespace must be absent from the unit'
assert 'sorry' in unit and unit.count(':=\n  sorry') == 1
os.makedirs(OUT, exist_ok=True)
open(os.path.join(OUT, 'Contract-mig0b-r2-unit.lean'), 'w', encoding='utf-8').write(unit)
json.dump({'landed_retired': LANDED_RETIRED, 'r1_retired': R1_RETIRED, 'blocks': manifest},
          open(os.path.join(OUT, 'manifest.json'), 'w', encoding='utf-8'), indent=1,
          ensure_ascii=False)
wide = [(i + 1, len(l)) for i, l in enumerate(unit.split('\n')) if len(l) > 100]
print('unit lines', unit.count('\n'), 'sha256', hashlib.sha256(unit.encode()).hexdigest())
print('blocks', len(manifest), 'landed taken', len(used['landed']), 'r1 taken', len(used['r1']))
print('lines over 100 code points:', wide)
