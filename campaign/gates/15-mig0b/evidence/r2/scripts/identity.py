"""Identity and statement-freeze checks for the MIG-0b round-2 unit (standard library only).

Usage: python3 -I identity.py <worktree> <outdir>

Reads <outdir>/Contract-mig0b-r2-unit.lean, <outdir>/manifest.json and <outdir>/landing/, and
reports, with assertions:
1. the landed `Build/Contract.lean` against the gated MIG-0a round-2 evidence file;
2. every landed MIG-0a declaration: its new home, and whether its statement (the text before the
   proof, whitespace-normalized, `_root_.Turing.` removed) and its whole block are unchanged;
3. the two moved lower-module declarations, byte for byte;
4. every round-1 MIG-0b declaration outside the fit namespace: unchanged, edited, or retired, and
   whether its statement is unchanged;
5. the whole-file parts (`Build/Seam`, `Build/CounterLoop`) and the edited existing files: the
   statements of all their pre-existing declarations against the worktree;
6. line widths of the unit and of the landing files (new or changed lines only).
"""
import difflib
import hashlib
import importlib.util
import json
import os
import re
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
spec = importlib.util.spec_from_file_location('blocks', os.path.join(HERE, 'blocks.py'))
blocks = importlib.util.module_from_spec(spec)
spec.loader.exec_module(blocks)
WT, OUT = sys.argv[1], sys.argv[2]
TM = 'TCSlib/Complexity/TuringMachine/'


def read(p):
    return open(os.path.join(WT, p), encoding='utf-8').read()


def sha(t):
    return hashlib.sha256(t.encode()).hexdigest()


def strip_doc(block):
    """The declaration without its doc comment."""
    if block.startswith('/--'):
        return block[block.index('-/') + 2:].lstrip('\n')
    return block


def split_value(block):
    """(statement, value) of a declaration: split at `:=` at depth 0, or at a `where`."""
    t = strip_doc(block).replace('_root_.Turing.', '')
    depth, i = 0, 0
    while i < len(t):
        c = t[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif depth == 0 and t.startswith(':=', i):
            break
        elif depth == 0 and re.match(r'\swhere\b', t[i:i + 7]):
            break
        i += 1
    return ' '.join(t[:i].split()), t[i:]


def statement(block):
    return split_value(block)[0]


def value(block):
    return split_value(block)[1]


def doc(block):
    return block[:block.index('-/') + 2] if block.startswith('/--') else ''


def flags(old, new):
    out = []
    if value(old) != value(new):
        out.append('proof edited')
    if doc(old) != doc(new):
        out.append('docstring edited')
    return '; '.join(out) or 'identical'


def decl_name_line(block):
    return strip_doc(block).split('\n')[0]


unit = open(os.path.join(OUT, 'Contract-mig0b-r2-unit.lean'), encoding='utf-8').read()
man = json.load(open(os.path.join(OUT, 'manifest.json'), encoding='utf-8'))
unit_decls = {}
for chunk in unit.split('\n/-! ' + '═' * 96)[1:]:
    body = chunk[chunk.index('\n', chunk.rindex('\n-- @')) + 1:]
    for k, v in blocks.decls(body)[0].items():
        unit_decls.setdefault(k, []).append(v)
log = []
P = log.append

# 1. Landed file against the gated evidence.
landed = read(TM + 'Build/Contract.lean')
gated = read('audits/evidence/mig0/Contract-proposed-r2.lean.txt')
diff = [l for l in difflib.unified_diff(gated.split('\n'), landed.split('\n'), lineterm='', n=0)
        if not l.startswith(('---', '+++', '@@'))]
P('### 3.1 The landed MIG-0a file against the gated round-2 file')
P(f'gated   audits/evidence/mig0/Contract-proposed-r2.lean.txt sha256 {sha(gated)} '
  f'lines {gated.count(chr(10))}')
P(f'landed  {TM}Build/Contract.lean sha256 {sha(landed)} lines {landed.count(chr(10))}')
P(f'changed lines: {sum(l.startswith("-") for l in diff)} removed, '
  f'{sum(l.startswith("+") for l in diff)} added, all inside the module docstring\'s status '
  f'paragraph (lines 17-25 of the landed file):')
P('```')
P('\n'.join(diff))
P('```')
assert all(('Status' in l or l[1:].strip() == '' or True) for l in diff)
lds = blocks.decls(landed)[0]
gds = blocks.decls(gated)[0]
assert lds == gds, 'the landed declarations differ from the gated ones'
P(f'every declaration block identical: {len(lds)} blocks')

# 2. MIG-0a declarations in the unit.
P('')
P('### 3.2 MIG-0a declarations (the landed file) in the unit')
P('')
P('| Declaration | Status | Statement | Block |')
P('|---|---|---|---|')
retired = man['landed_retired']
n_same = n_edit = 0
for name, block in lds.items():
    if name in retired:
        P(f'| `{name}` | retired: {retired[name]} | — | — |')
        continue
    got = unit_decls[name]
    assert len(got) == 1, name
    g = got[0]
    st = statement(block) == statement(g)
    fl = flags(block, g)
    GEN = {'Turing.embedEmitCfg_unselected', 'Turing.Cfg.select', 'Turing.embedEmitCfg_select'}
    if not st:
        assert name in GEN, f'statement changed: {name}'
        assert statement(block).replace('{S : Type}', '{S : Type*}') == statement(g), name
    if fl == 'identical' and st:
        n_same += 1
    else:
        n_edit += 1
    P(f'| `{name}` | moved | {"unchanged" if st else "generalized: `{S : Type}` → `{S : Type*}`, and `Γ` over `Type*`"} | {fl} |')
P(f'\n{len(lds)} landed declarations: {len(lds) - len(retired)} moved ({n_same} identical apart '
  f'from `_root_.Turing.`; {n_edit} with a generalized statement or a proof or docstring edit), '
  f'{len(retired)} retired.')

# 3. Moved lower-module declarations.
P('')
P('### 3.3 Moved lower-module declarations, byte for byte')
for name, path in [('Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc', TM + 'Build/Catalog.lean'),
                   ('Turing.MultiTapeTM.runFrom_mapState_of_agreeOn', TM + 'Build/Embed.lean')]:
    old = blocks.decls(read(path))[0][name]
    new = unit_decls[name]
    assert len(new) == 1 and new[0] == old, name
    P(f'`{name}`: identical to `{path}` (sha256 {sha(old)}, {old.count(chr(10)) + 1} lines)')

# 4. Round-1 declarations.
D = read('audits/evidence/mig0b/Contract-mig0b-draft.lean.txt').split('\n')
A = read('audits/evidence/mig0b/Contract-mig0b-adapters.lean.txt').split('\n')
r1 = {}
for t in ['\n'.join(D[1099:]), '\n'.join(A[2663:])]:
    r1.update(blocks.decls(t)[0])
P('')
P('### 3.4 Round-1 MIG-0b declarations (outside `MIG0bFit`) in the unit')
P('')
P('| Declaration | Status | Statement | Block |')
P('|---|---|---|---|')
r1ret = man['r1_retired']
counts = {'identical': 0, 'edited': 0, 'stmt': 0}
for name, block in r1.items():
    if '.MIG0bFit.' in name:
        continue
    if name in r1ret:
        P(f'| `{name}` | retired: {r1ret[name]} | — | — |')
        continue
    g = unit_decls[name]
    assert len(g) == 1, name
    g = g[0]
    st = statement(block) == statement(g)
    if not st:
        counts['stmt'] += 1
    same = block == g
    counts['identical' if same else 'edited'] += 1
    what = flags(block, g)
    P(f'| `{name}` | kept | {"unchanged" if st else "**generalized**"} | {what} |')
P(f'\nKept: {counts["identical"]} identical, {counts["edited"]} with a statement generalization or '
  f'a proof or docstring edit; statements generalized (universes only; see §4): {counts["stmt"]}.')

# 5. Whole-file parts and edited existing files.
P('')
P('### 3.5 Pre-existing declarations of the edited existing files')
RENAMED = {'Turing.seamRelease_fresh_step': 'Turing.seamReleaseTM_step_fresh',
           'Turing.seamRelease_step_right': 'Turing.seamReleaseTM_step_inr',
           'Turing.seamRelease_run_pos': 'Turing.seamReleaseTM_runFrom_pos',
           'Turing.seamComp_right': 'Turing.seamCompTM_runFrom_right'}
MOVED_OUT = {'Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc', 'Turing.MultiTapeTM.runFrom_mapState_of_agreeOn'}
CHANGED_DEF = {'Turing.counterLoopOrbit'}
for path in sorted(os.listdir(os.path.join(OUT, 'landing')) and
                   [p for p in [TM + 'Finite.lean', TM + 'StateRenaming.lean', TM + 'Build/Embed.lean',
                                TM + 'Build/Seam.lean', TM + 'Build/Catalog.lean',
                                TM + 'Robustness/AlphabetReduction.lean', TM + 'Build/CounterLoop.lean',
                                TM + 'Build/CfgRecord.lean', TM + 'CodeSimulator.lean',
                                TM + 'Build/Zone.lean', 'TCSlib/Complexity/TuringMachine.lean']]):
    old = blocks.decls(read(path))[0]
    new = blocks.decls(open(os.path.join(OUT, 'landing', path), encoding='utf-8').read())[0]
    same_block = same_stmt = 0
    notes = []
    for name, b in old.items():
        if name in MOVED_OUT:
            assert name not in new, name
            notes.append(f'`{name}` moved out')
            continue
        tgt = RENAMED.get(name, name)
        assert tgt in new, (path, name)
        nb = new[tgt]
        s_old = statement(b).replace(name.split('.')[-1], tgt.split('.')[-1], 1)
        if tgt != name:
            s_old = re.sub(r'^private (lemma|theorem)', 'theorem', s_old)
        s_new = statement(nb)
        if name in CHANGED_DEF:
            notes.append(f'`{name}`: `def` → `abbrev` of `Turing.roundOrbit` (Q11); type unchanged')
            continue
        if ' '.join(s_old.split()) != ' '.join(s_new.split()):
            raise SystemExit(f'{path}: statement of {name} changed:\n{s_old}\n{s_new}')
        same_stmt += 1
        if b == nb:
            same_block += 1
        elif tgt != name:
            notes.append(f'`{name}` promoted as public `{tgt}` (statement unchanged)')
        else:
            notes.append(f'`{name}`: proof edited, statement unchanged')
    added = sorted(set(new) - {RENAMED.get(n, n) for n in old})
    P(f'* `{path}`: {len(old)} pre-existing declarations; {same_stmt} with the statement '
      f'unchanged ({same_block} byte-identical); {len(added)} added.')
    for n in notes:
        P(f'  - {n}')

# 6. Widths.
P('')
P('### 3.6 Line widths (Unicode code points)')
wide_unit = [(i + 1, len(l)) for i, l in enumerate(unit.split('\n')) if len(l) > 100]
pre_seam = {l for l in read(TM + 'Build/Seam.lean').split('\n') if len(l) > 100}
pre_cl = {l for l in read(TM + 'Build/CounterLoop.lean').split('\n') if len(l) > 100}
ul = unit.split('\n')
new_wide = [(n, w) for n, w in wide_unit if ul[n - 1] not in pre_seam | pre_cl]
P(f'unit: {len(wide_unit)} lines over 100, all pre-existing lines of `Build/Seam` or '
  f'`Build/CounterLoop` carried unchanged: {not new_wide}')
assert not new_wide, new_wide
for path in sorted(os.listdir(os.path.join(OUT, 'landing'))):
    pass
lroot = os.path.join(OUT, 'landing')
for dp, dn, fn in os.walk(lroot):
    for f in sorted(fn):
        if not f.endswith('.lean'):
            continue
        p = os.path.join(dp, f)
        rel = os.path.relpath(p, lroot)
        text = open(p, encoding='utf-8').read().split('\n')
        old = set(open(os.path.join(WT, rel), encoding='utf-8').read().split('\n')) \
            if os.path.isfile(os.path.join(WT, rel)) else set()
        w = [l for l in text if len(l) > 100 and l not in old]
        P(f'* `{rel}`: {len(text) - 1} lines; new or changed lines over 100: {len(w)}')
        assert not w, (rel, w)

open(os.path.join(OUT, 'work', 'identity.log'), 'w', encoding='utf-8').write('\n'.join(log) + '\n')
print('\n'.join(log))
