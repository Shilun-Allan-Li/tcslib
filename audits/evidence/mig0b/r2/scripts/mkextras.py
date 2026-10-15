"""Landing tree, edited existing files, downstream probes and the fit file (standard library only).

Usage: python3 -I mkextras.py <worktree> <unit.lean> <outdir>

Writes:
* <outdir>/landing/<path>.lean — every file the landing PR writes, in full: the new modules and the
  whole-file parts of the unit (header, imports, options, body), and the existing modules that the
  unit appends to or edits, as edited (Finite, StateRenaming, Build/Embed, Build/Catalog,
  Robustness/AlphabetReduction), plus the consumer edits that Q11's abbreviation needs
  (Build/CfgRecord, CodeSimulator) and one docstring (Build/Zone);
* <outdir>/landing/<path>.diff — a unified diff against the worktree for every existing file;
* <outdir>/extras.lean — extras parts for cutcheck2.py: each edited existing file as a whole-file
  part in its own closure, the downstream probes of `counterLoopOrbit`'s consumers (with and
  without their edits), and the fit-test file over every landing module.
Every edit is an exact replacement asserted to match the stated number of times.
"""
import difflib
import importlib.util
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def load(name):
    spec = importlib.util.spec_from_file_location(name, os.path.join(HERE, name + '.py'))
    m = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(m)
    return m


cc = load('cutcheck2')
WT, UNIT, OUT = sys.argv[1], sys.argv[2], sys.argv[3]
TM = 'TCSlib/Complexity/TuringMachine/'
parts = {p['index']: p for p in cc.parse(UNIT)}


def read(p):
    return open(os.path.join(WT, p), encoding='utf-8').read()


def edit(text, edits, label):
    for e in edits:
        old, new = e[0], e[1]
        n = e[2] if len(e) > 2 else 1
        c = text.count(old)
        assert c == n, f'{label}: edit expects {n} match(es), found {c}: {old[:70]!r}'
        text = text.replace(old, new)
    return text


def body(i):
    return '\n'.join(parts[i]['body']).strip('\n') + '\n'


def header_split(text):
    """(copyright+imports+options, rest) of a module file: split before the first `/-!`."""
    i = text.index('\n/-!')
    return text[:i + 1], text[i + 1:]


def full_module(imports, rest):
    return (cc.COPYRIGHT + ''.join(f'import {m}\n' for m in imports) + '\n' + cc.OPTIONS + '\n'
            + rest.strip('\n') + '\n')


def cut_block(text, start, end_marker, label):
    """Delete from the line `start` (inclusive) to just before `end_marker` (asserted unique)."""
    assert text.count(start) == 1, label
    s = text.index(start)
    e = text.index(end_marker, s)
    return text[:s] + text[e:]


landing = {}  # path -> text

# New modules and whole-file parts of the unit.
for i, p in parts.items():
    path = p['land'].replace('.', '/') + '.lean'
    k = cc.kind(WT, p)
    if k in ('new', 'replace'):
        landing[path] = full_module(p['imports'], body(i))

# Finite: parts 1 and 2 appended; module docstring.
fin = read(TM + 'Finite.lean')
fin = edit(fin, [(
    '  argument, public for the oracle query capture; added 2026-10-11, B1).\n',
    '  argument, public for the oracle query capture; added 2026-10-11, B1).\n'
    '* `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — a head confined to an integer interval\n'
    '  visits at most its cardinality (moved from `Build/Catalog` at MIG-0b\'s layering split, for\n'
    '  the contract core, 2026-10-13).\n'
    '* `Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc` — after `u` steps every work head lies\n'
    '  within `u` cells of its start (MIG-0b, 2026-10-13).\n')], 'Finite doc')
landing[TM + 'Finite.lean'] = fin.rstrip('\n') + '\n\n' + body(1) + '\n' + body(2)

# StateRenaming: imports Simulation; part 3 appended; module docstring.
sr = read(TM + 'StateRenaming.lean')
sr = edit(sr, [
    ('import TCSlib.Complexity.TuringMachine.Deterministic\n',
     'import TCSlib.Complexity.TuringMachine.Deterministic\n'
     'import TCSlib.Complexity.TuringMachine.Simulation\n'),
    ('* `Turing.MultiTapeTM.relabelState_runFrom_init` — initialized runs correspond\n'
     '  at every time.\n',
     '* `Turing.MultiTapeTM.relabelState_runFrom_init` — initialized runs correspond\n'
     '  at every time.\n'
     '* `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` — injective state transport\n'
     '  followed by guarded agreement on the host carrier (moved from `Build/Embed` at\n'
     '  MIG-0b\'s layering split, 2026-10-13, so that the contract core can rename states;\n'
     '  hence the import of `Simulation`, for `AgreeOn`).\n'),
], 'StateRenaming')
landing[TM + 'StateRenaming.lean'] = sr.rstrip('\n') + '\n\n' + body(3)

# Build/Embed: imports Convention; the moved block deleted; part 4 appended; module docstring.
emb = read(TM + 'Build/Embed.lean')
emb = edit(emb, [
    ('import TCSlib.Complexity.TuringMachine.StateRenaming\n',
     'import TCSlib.Complexity.TuringMachine.StateRenaming\n'
     'import TCSlib.Complexity.TuringMachine.Build.Convention\n'),
    ('* `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn` — injective state transport\n'
     '  followed by guarded agreement on the host carrier.\n',
     '* `Turing.embedEmitCfg_unselected`, `Turing.embedEmitCfg_select` — the frame export and\n'
     '  the selection identity (moved from `Build/Contract.lean` at MIG-0b\'s layering split).\n'
     '* `Turing.embedEmitCfg_eq`, `Turing.embedEmitCfg_mapState_eq`,\n'
     '  `Turing.embedEmitCfg_ofWords_eq` — the R1 reconstruction lemma and its corollaries\n'
     '  (MIG-0b; the wave-1 fill gate\'s major F1). `Turing.MultiTapeTM.runFrom_mapState_of_agreeOn`\n'
     '  moved to `StateRenaming` at MIG-0b.\n'),
    ('* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning\n',
     '* `Turing.Cfg.select` — the selected bank of a host configuration, with empty output\n'
     '  (moved from `Build/Contract.lean` at MIG-0b\'s layering split).\n'
     '* `Turing.embedSilentRetTM`, `Turing.embedEmitRetTM` — the two returning\n'),
], 'Embed')
emb = cut_block(emb, '/-! ## Guarded state transport -/\n', '\nend Turing', 'Embed moved block')
landing[TM + 'Build/Embed.lean'] = emb.rstrip('\n') + '\n\n' + body(4)

# Build/Catalog: the moved block deleted; module docstring.
cat = read(TM + 'Build/Catalog.lean')
cat = edit(cat, [(
    '* `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — a head confined to an\n'
    '  integer interval visits at most its cardinality (the head-interval bound\n'
    '  the Z4 space annotation consumes). (Moved from `Build/Zone.lean` for B4,\n'
    '  2026-10-12.)',
    '* `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` — the head-interval bound the\n'
    '  Z4 space annotation consumes — moved on to `Finite` at MIG-0b\'s layering split\n'
    '  (2026-10-13; it was here from `Build/Zone.lean` for B4, 2026-10-12).')], 'Catalog doc')
cat = cut_block(cat, '/-- A head confined to an integer interval visits at most its cardinality.\n',
                '/-- A head confined to the inclusive interval from minus one to `L` visits',
                'Catalog moved block')
landing[TM + 'Build/Catalog.lean'] = cat

# Robustness/AlphabetReduction: imports the core; part 7 appended; module docstring.
ar = read(TM + 'Robustness/AlphabetReduction.lean')
ar = edit(ar, [
    ('import Mathlib.Tactic.Ring\n',
     'import Mathlib.Tactic.Ring\nimport TCSlib.Complexity.TuringMachine.Build.Contract.Basic\n'),
    ('* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].\n',
     '* `Turing.FinTM.alphabet_reduction` — [AB09, Claim 1.5].\n'
     '* `Turing.FinTM.exists_alphabetReduction_lockstep` (admitted; RS-5),\n'
     '  `Turing.FinTM.alphabetReduction_contract` — the simulation as a macro-step lockstep, and as\n'
     '  a contract-to-contract theorem (MIG-0b).\n'),
], 'AlphabetReduction')
landing[TM + 'Robustness/AlphabetReduction.lean'] = ar.rstrip('\n') + '\n\n' + body(7)

# Q11's consumers outside CounterLoop: the proofs that unfold `counterLoopOrbit`.
Q11 = {
    TM + 'Build/CfgRecord.lean': [('rw [counterLoopOrbit, Function.iterate_succ_apply\']',
                                   'rw [counterLoopOrbit, roundOrbit, Function.iterate_succ_apply\']',
                                   2)],
    TM + 'CodeSimulator.lean': [('    simp only [counterLoopOrbit, Function.iterate_succ_apply\']\n',
                                 '    simp only [counterLoopOrbit, roundOrbit, Function.iterate_succ_apply\']\n')],
}
for path, es in Q11.items():
    landing[path] = edit(read(path), es, path)

# Build/Zone: the docstring that names the lemma's home.
zone = read(TM + 'Build/Zone.lean')
landing[TM + 'Build/Zone.lean'] = edit(zone, [(
    '  `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` (moved to\n'
    '  `Build/Catalog.lean` for B4, 2026-10-12).',
    '  `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc` (moved to\n'
    '  `Build/Catalog.lean` for B4, 2026-10-12, and to `Finite.lean` at MIG-0b).')], 'Zone')

# The TuringMachine facade: its entry for Build/Contract.
tmf = read('TCSlib/Complexity/TuringMachine.lean')
landing['TCSlib/Complexity/TuringMachine.lean'] = edit(tmf, [(
    '* `Build/Contract` — the framed-contract structure (MIG-0a, `machine-library-design.md` §16a):\n'
    '  exact time, an endpoint function, an exit set with a no-earlier-exit cut and head envelopes, a\n'
    '  derived frames layer, and the compositions `trans`, `seq`, `inPhase`, `embed`, `branch` and\n'
    '  `ReturnContract.release` as thin wrappers over the public rows. Proved; MIG-0a gate closed.\n',
    '* `Build/Contract` — the framed-contract library (MIG-0a and MIG-0b, `machine-library-design.md`\n'
    '  §16a), the facade of `Build/Contract/{Basic,Seam,Embed,Catalog,Lift}`: exact time, an endpoint\n'
    '  function, an exit set with a no-earlier-exit cut and head envelopes, a derived frames layer,\n'
    '  the compositions `trans`, `seq`, `inPhase`, `embed`, `branch` and the releases as thin\n'
    '  wrappers over the public rows, and the segment, round and joint-trajectory layers with state\n'
    '  renaming and the macro-step lockstep. The core, `Build/Contract/Basic`, imports only the\n'
    '  machine core.\n')], 'TuringMachine facade')

for path, text in landing.items():
    dst = os.path.join(OUT, 'landing', path)
    os.makedirs(os.path.dirname(dst), exist_ok=True)
    open(dst, 'w', encoding='utf-8').write(text)
    src = os.path.join(WT, path)
    if os.path.isfile(src):
        old = open(src, encoding='utf-8').read()
        d = ''.join(difflib.unified_diff(old.splitlines(True), text.splitlines(True),
                                         'a/' + path, 'b/' + path, n=3))
        open(dst[:-5] + '.diff', 'w', encoding='utf-8').write(d)

# ── The extras file ──────────────────────────────────────────────────────────────────────────

xs = []


def xpart(n, title, land, imports, text, exclude=(), with_=()):
    n = 101 + len(xs)  # the index cutcheck2.py assigns
    lines = [cc.HEADER + '═' * 92, f'Extras part {n}. {title} -/', f'-- @landing {land}']
    if exclude:
        lines.append('-- @exclude-parts ' + ' '.join(map(str, exclude)))
    if with_:
        lines.append('-- @with ' + ' '.join(map(str, with_)))
    lines.append('-- @imports ' + ' '.join(imports))
    xs.append('\n'.join(lines) + '\n' + text.strip('\n') + '\n')


def imports_of(text):
    return [l.split()[1] for l in text.split('\n') if l.startswith('import ')]


def rest_of(text):
    return header_split(text)[1]


M = 'TCSlib.Complexity.TuringMachine.'
for n, (path, mod, excl) in enumerate([
        (TM + 'Finite.lean', M + 'Finite', (1, 2)),
        (TM + 'StateRenaming.lean', M + 'StateRenaming', (3,)),
        (TM + 'Build/Embed.lean', M + 'Build.Embed', (4,)),
        (TM + 'Build/Catalog.lean', M + 'Build.Catalog', ()),
        (TM + 'Robustness/AlphabetReduction.lean', M + 'Robustness.AlphabetReduction', (7,))],
        start=101):
    t = landing[path]
    xpart(n, f'`{path}` as edited, whole file, in its own closure.', mod, imports_of(t),
          rest_of(t), exclude=excl)

# Downstream probes of Q11 (old Build/Seam kept: part 5 excluded; its changes are unrelated).
IC, CR = TM + 'Build/InputCall.lean', TM + 'Build/CfgRecord.lean'
INC, CS, IL = ('TCSlib/Complexity/SpaceComplexity/Inclusions.lean', TM + 'CodeSimulator.lean',
               TM + 'Build/InputLength.lean')
probes = [
    (106, IC, M + 'Build.InputCall', read(IC), (), 'verbatim'),
    (107, CR, M + 'Build.CfgRecord', landing[CR], (106,), 'with its Q11 edit'),
    (108, INC, 'TCSlib.Complexity.SpaceComplexity.Inclusions', read(INC), (),
     'verbatim (its `simpa only [counterLoopOrbit, …]` still closes)'),
    (109, CS, M + 'CodeSimulator', landing[CS], (106,), 'with its Q11 edit'),
    (110, IL, M + 'Build.InputLength', read(IL), (), 'verbatim'),
    (111, CR, M + 'Build.CfgRecord', read(CR), (106,), 'UNEDITED (negative control)'),
    (112, CS, M + 'CodeSimulator', read(CS), (106,), 'UNEDITED (negative control)'),
]
for n, path, mod, t, w, what in probes:
    xpart(n, f'Downstream probe: `{path}`, {what}, over the new `Build/CounterLoop`.', mod,
          imports_of(t), rest_of(t), exclude=(5,), with_=w)

# The fit-test file: over every landing module.
spec = importlib.util.spec_from_file_location('blocks', os.path.join(HERE, 'blocks.py'))
blocks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(blocks)
D = read('audits/evidence/mig0b/Contract-mig0b-draft.lean.txt').split('\n')
A = read('audits/evidence/mig0b/Contract-mig0b-adapters.lean.txt').split('\n')
dsec, asec = '\n'.join(D[1099:]), '\n'.join(A[2663:])
s = dsec.index('/-! ## Fit tests')
e = dsec.index('end MIG0bFit\n') + len('end MIG0bFit\n')
fit_r1 = dsec[s:e]
adecls = blocks.decls(asec)[0]
fit_r1_a = '\n\n'.join(adecls['Turing.MIG0bFit.' + n] for n in
                       ['counterSpan', 'counterSpan_iff_segment', 'counter_span_append',
                        'counterSpan_zero'])
NEW = {}
cur = None
for line in open(os.path.join(HERE, '..', 'src', 'new.lean'), encoding='utf-8').read().split('\n'):
    if line.startswith('-- %%% '):
        cur = line[7:].strip()
        NEW[cur] = []
    else:
        NEW[cur].append(line)
NEW = {k: '\n'.join(v).strip('\n') for k, v in NEW.items()}
fit_body = '\n\n'.join([NEW['fit_head'], fit_r1.strip('\n'), fit_r1_a, NEW['fit_extra'],
                        NEW['fit_tail']]) + '\n'
xpart(120, 'The fit tests (round 1, unchanged) and the round-2 checks, over every landing module '
      '(not for landing).', 'TCSlib.Evidence.MIG0bR2Fit',
      [M + 'Build.Contract', M + 'Build.CounterLoop', M + 'Robustness.AlphabetReduction',
       'Mathlib.Tactic.Linarith'], fit_body)
open(os.path.join(OUT, 'fit-tests.lean'), 'w', encoding='utf-8').write(fit_body)

head = ('/-! Extras for `cutcheck2.py` (generated by `mkextras.py`; not landing material except '
        'that\nparts 101–105 are the edited existing files that `landing/` also holds). -/\n\n')
open(os.path.join(OUT, 'extras.lean'), 'w', encoding='utf-8').write(head + '\n'.join(xs))
print('landing files', len(landing), 'extras parts', len(xs))
for path in sorted(landing):
    print(f'  {path}: {landing[path].count(chr(10))} lines')
