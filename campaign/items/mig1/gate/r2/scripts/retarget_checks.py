"""MIG-1 statement gate, round 2: Lean checks of the non-verbatim retargets in the Loop home.

Usage: python3 -I retarget_checks.py <worktree> <deletion-plan.json> <overlay part1.lean> <outdir>

For every region copy whose source is in `Build/Loop.lean` and whose code is not identical to its
source (the old-host phase lemmas: modified and statement-identical copies), the copy's statement
(comment-stripped, region names unprefixed, `private lemma f2_X` -> `example`) is restated and
proved from the retarget in one step: `apply X (forward := false) <;> assumption` (`(pre := [])`
added where the source has an output-prefix parameter), `apply X <;> assumption` where the source
has no forwarding parameter. A restated copy that is stronger than its retarget fails. Also
restated: Catalog's `f2_head_steps`, proved from the MIG-0b stand-in by `Finset.mem_Icc.mp`.

Writes <outdir>/RetargetChecks-r2.lean (overlay part 1, the repaired Loop, then the examples) and
<outdir>/RetargetChecks-tip.lean (the tip's Loop verbatim, then the same examples except the head
example, whose stand-in the tip lacks): the negative control. Expected: the r2 file elaborates
without errors; the tip file fails exactly at two examples: `loopHost_prepare` (finding 1: the
original lacks the fuel-head clause) and `loopHost_contracts` (the original lacks the two head
clauses; the round-1 plan already replaces it by the moved copy). The moved contract's example
re-packs the explicit coefficient: `⟨10, loopHost_contracts …⟩`.
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import region as RG  # noqa: E402
from decls import scan  # noqa: E402

WT, PLAN, PART1, OUT = sys.argv[1:5]


LET = re.compile(r'\b(let|have)\s+[^\s:=()]+(\s*:[^=]*)?\s*$')


def top_assign(text):
    """Index of the `:=` that opens the proof: the first one at bracket depth zero that does
    not bind a `let`/`have` inside the statement (`f2_loopHost_round` states `let start := …`)."""
    depth = 0
    for i, ch in enumerate(text):
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and text.startswith(':=', i) and not LET.search(text[:i]):
            return i
    raise AssertionError(text[:200])


plan = json.load(open(PLAN, encoding='utf-8'))
rows = plan['rows']
names = {r['name'] for r in rows}
rmap = {n: RG.unprefix(n) for n in names if RG.unprefix(n)}
cat_path = os.path.join(WT, RG.CATALOG)
cat_code = RG.strip_comments(open(cat_path, encoding='utf-8').read().split('\n'))
D, _ = scan(cat_path)
dl = {d['name']: d for d in D if plan['region'][0] < d['line'] < plan['region'][1]}
loop_path = os.path.join(WT, RG.HOMES['Loop'])
loop_code = RG.strip_comments(open(loop_path, encoding='utf-8').read().split('\n'))
LD, _ = scan(loop_path)
ld = {d['line']: d for d in LD}


def wrap(line):
    """Break a statement line over 100 columns at a space inside parentheses (layout-neutral
    in a term), the continuation indented four more columns."""
    out = []
    while len(line) > 100:
        ind = len(line) - len(line.lstrip())
        depth, cut = 0, None
        for i, ch in enumerate(line):
            if ch in '([{⟨':
                depth += 1
            elif ch in ')]}⟩':
                depth -= 1
            elif ch == ' ' and depth > 0 and ind < i <= 98:
                cut = i
        assert cut is not None, line
        out.append(line[:cut])
        line = ' ' * (ind + 4) + line[cut + 1:]
    return out + [line]


def restated(name):
    code = '\n'.join(RG.rename(RG.code_of(cat_code, dl[name]), rmap))
    code = '\n'.join(w for l in code.split('\n') for w in wrap(l))
    stmt = code[:top_assign(code)].rstrip()
    first, rest = stmt.split('\n', 1)
    head = 'private lemma ' + RG.unprefix(name) + ' '
    assert first.startswith(head), first
    return '/-- Restates the copy ' + name + ' (statement only). -/\nexample ' + \
        first[len(head):] + '\n' + rest, code


examples, report = [], []
for r in rows:
    src = r.get('source') or ''
    if not src.startswith('Loop:') or r.get('code_identical') or r['kind'] != 'lemma':
        continue
    _, ln, base = src.split(':')
    scode = '\n'.join(RG.code_of(loop_code, ld[int(ln)]))
    sstmt = scode[:top_assign(scode)]
    named = ''
    if re.search(r'\((?:[^():]*\s)?forward(?:\s[^():]*)?\s*:\s*Bool\)', sstmt):
        named += ' (forward := false)'
    if '(pre : List Bool)' in sstmt:
        named += ' (pre := [])'
    text, _ = restated(r['name'])
    if r['name'] == 'f2_loopHost_contracts':
        # the moved contract is the copy with `∃ c` removed and `c ↦ 10`: re-pack the witness
        ex = text + ' :=\n  ⟨10, loopHost_contracts body F anchor Inv stepF acceptF out findMode s0 R T' \
            ' hF\n    hInv0 hInvStep hstart hround⟩\n'
        named = '⟨10, ·⟩ (the witness re-packed)'
    else:
        ex = text + ' := by\n  apply ' + base + named + ' <;> assumption\n'
    examples.append((r['name'], ex))
    report.append((r['name'], base, named.strip() or '(none)', r['fate']))

head_ex = restated('f2_head_steps')[0] + \
    ' :=\n  Finset.mem_Icc.mp (mig0bStandIn_workTapePos_runFrom_mem_Icc M c t i)\n'

hdr = ('\n/-! Retarget checks (MIG-1 round 2, not landed): each Loop-sourced non-identical copy\n'
       'of the Catalog region, restated, follows from its retarget in one step. -/\n\n'
       'namespace Turing.FinTM\n\n')
body = '\n'.join(ex for _, ex in examples)
part1 = open(PART1, encoding='utf-8').read()
tip = open(loop_path, encoding='utf-8').read()
r2 = part1.rstrip('\n') + '\n' + hdr + body + '\n' + head_ex + '\nend Turing.FinTM\n'
neg = tip.rstrip('\n') + '\n' + hdr + body + '\nend Turing.FinTM\n'
os.makedirs(OUT, exist_ok=True)
for fn, t in [('RetargetChecks-r2.lean', r2), ('RetargetChecks-tip.lean', neg)]:
    wide = [l for l in t.split('\n')[t[:t.index(hdr)].count('\n'):] if len(l) > 100]
    assert not wide, wide[:3]
    open(os.path.join(OUT, fn), 'w', encoding='utf-8').write(t)
with open(os.path.join(OUT, 'retarget-checks.tsv'), 'w', encoding='utf-8') as f:
    f.write('copy\tretarget (Build/Loop.lean)\tnamed arguments\tround-2 fate\n')
    for row in report:
        f.write('\t'.join(row) + '\n')
    f.write('f2_head_steps\tworkTapePos_runFrom_mem_Icc (MIG-0b; stand-in)\tFinset.mem_Icc.mp\t'
            'delete: duplicates an existing public declaration\n')
print('examples:', len(examples) + 1, '(r2 file);', len(examples), '(tip file)')
for row in report:
    print('  ', row[0], '->', row[1], row[2])
