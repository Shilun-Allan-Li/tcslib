"""MIG-1 statement gate, round 2: the systematic retarget check over the deletion plan.

Usage: python3 -I retarget.py <worktree> <deletion-plan.json> <unit.lean> <mig0b Finite.lean>
                              <retarget-checks.tsv> <out.tsv>

Read-only on its inputs; standard library only. For every region declaration whose fate moves it
into a home (`move*`) or absorbs it into a gated statement (`absorbed*`), and for every region
name its code cites (statement and proof; `region.py`'s `uses`), the row records the cited name's
round-2 fate, its retarget, where the retarget lives and whether it is private, and a statement
comparison:

* statements are comment-stripped, whitespace-normalized and cut at the `:=` that opens the
  proof (bracket depth zero, not the binder of a `let`/`have` inside the statement; round 1's
  `region.statement` cut `f2_loopHost_round` at its `let start :=`, which this repairs), with
  the region's prefix map (`f2_X -> X`, `catalog_redirectX -> redirectX`) and the moved-name map
  applied to the copy;
* classes: IDENTICAL; MOVES-WITH (the cited name moves to the same home under the moved-name
  map: the same text); GENERALIZATION (a named instantiation, checked by Lean in
  `checks/RetargetChecks-r2.lean`, or by the bridge probe for the duplicates of public lemmas);
  WEAKER; NOT-CARRIED (the citer's proof is replaced, not moved, so the citation does not reach
  the home); PROBLEM (the cited name is deleted without a retarget).
* accessibility: a private retarget must live in the citer's receiving home; a public one must
  be in the receiving home's import closure (`closure` below, from the `import` lines of the
  worktree and of its Mathlib package; MIG-0b's Finite counts as Finite, the decision-4 import
  of `Mathlib.Algebra.BigOperators.Fin` in Simulation is recorded as a condition).

Prints the population, the class counts and every row that is not IDENTICAL or MOVES-WITH.
"""
import json
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import region as RG  # noqa: E402
from decls import scan  # noqa: E402

WT, PLAN, UNIT, FINITE, CHECKS, OUT = sys.argv[1:7]
T = 'TCSlib.Complexity.'
MODS = {'Simulation': T + 'TuringMachine.Simulation', 'Composition': T + 'TuringMachine.Composition',
        'Wrappers': T + 'TuringMachine.Build.Wrappers', 'Encoding': T + 'TuringMachine.Encoding',
        'TimeConstructible': T + 'ClassP.TimeConstructible', 'Loop': T + 'TuringMachine.Build.Loop',
        'Primitives': T + 'TuringMachine.Build.Primitives',
        'Catalog': T + 'TuringMachine.Build.Catalog'}
HOME_OF_PATH = {'Build/Loop.lean': 'Loop', 'Build/Primitives.lean': 'Primitives',
                'Build/Wrappers.lean': 'Wrappers', 'ClassP/TimeConstructible.lean': 'TimeConstructible',
                'TuringMachine/Simulation.lean': 'Simulation'}
LET = re.compile(r'\b(let|have)\s+[^\s:=()]+(\s*:[^=]*)?\s*$')
ML = os.path.join(WT, '.lake/packages/mathlib')


def imports(mod):
    root = WT if mod.startswith('TCSlib') else ML if mod.startswith('Mathlib') else None
    if root is None:
        return []
    p = os.path.join(root, mod.replace('.', '/') + '.lean')
    if not os.path.isfile(p):
        return []
    return [l.split()[1] for l in open(p, encoding='utf-8') if l.startswith('import ')]


def closure(mod):
    seen, st = set(), [mod]
    while st:
        for y in imports(st.pop()):
            if y not in seen:
                seen.add(y)
                st.append(y)
    return seen


def statement(lines):
    text = '\n'.join(lines)
    depth = 0
    for i, ch in enumerate(text):
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif depth == 0 and text.startswith(':=', i) and not LET.search(text[:i]):
            return ' '.join(text[:i].split())
        elif depth == 0 and text.startswith(' where', i) and (i + 6 == len(text) or text[i + 6] in ' \n'):
            return ' '.join(text[:i].split())
    return ' '.join(text.split())


def body_stmt(st):
    """The statement without its keyword, modifiers and name (for comparisons across names)."""
    m = re.match(r'^(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|instance|'
                 r'inductive|structure)\s+\S+\s*(.*)$', st)
    return (m.group(1), m.group(2)) if m else (None, st)


plan = json.load(open(PLAN, encoding='utf-8'))
rows = plan['rows']
by = {r['name']: r for r in rows}
names = set(by)
moved = {r['name']: r['new_name'].split('.')[-1] for r in rows if r.get('new_name')}
rmap = {n: RG.unprefix(n) for n in names if RG.unprefix(n)}
rmap.update(moved)
cat_path = os.path.join(WT, RG.CATALOG)
cat_code = RG.strip_comments(open(cat_path, encoding='utf-8').read().split('\n'))
CD, _ = scan(cat_path)
cd = {d['name']: d for d in CD if plan['region'][0] < d['line'] < plan['region'][1]}
homes = {}
for k, rel in RG.HOMES.items():
    p = os.path.join(WT, rel)
    hd, _ = scan(p)
    homes[k] = (RG.strip_comments(open(p, encoding='utf-8').read().split('\n')), hd)
ucode = RG.strip_comments(open(UNIT, encoding='utf-8').read().split('\n'))
UD, _ = scan(UNIT)
fcode = RG.strip_comments(open(FINITE, encoding='utf-8').read().split('\n'))
FD, _ = scan(FINITE)
checked = {}
for l in open(CHECKS, encoding='utf-8').read().split('\n')[1:]:
    if l.strip():
        c = l.split('\t')
        checked[c[0]] = c[2]
clos = {k: closure(m) for k, m in MODS.items()}


def copy_stmt(n):
    return statement(RG.rename(RG.code_of(cat_code, cd[n]), rmap))


def home_stmt(k, line=None, name=None):
    code, hd = homes[k]
    d = [x for x in hd if (line and x['line'] == line) or (name and x['name'] == name)]
    assert len(d) == 1, (k, line, name)
    return statement(RG.code_of(code, d[0])), d[0]['private'], d[0]['line']


def unit_stmt(short):
    d = [x for x in UD if x['name'] == short]
    assert len(d) == 1, short
    return statement(RG.code_of(ucode, d[0])), d[0]['private']


def receiving(r):
    f = r['fate']
    if f.startswith('move: replaces'):
        return 'Loop', True
    if f.startswith('move (statement'):
        return 'Simulation', True
    if f.startswith('move'):
        return HOME_OF_PATH[r['detail'].split(' (')[0]], True
    if f.startswith('absorbed'):
        home = r['detail'].split('(')[1].split(';')[0].strip()
        carried = r['name'] in PROOF_MOVES
        return home, carried
    raise AssertionError(r['name'])


# absorbed declarations whose proofs move as the specs' proofs (round-1 pack, deletion plan)
PROOF_MOVES = {'f2_counter_space', 'f2_cond_space', 'f2_branch_space', 'f2_exists_loopFind_space',
               'f2_space_of_time'}
DUP = {  # duplicates of public declarations: (retarget, where, evidence)
    'f2_head_steps': ('Turing.MultiTapeTM.workTapePos_runFrom_mem_Icc', 'Finite (MIG-0b)',
                      'Lean: checks/RetargetChecks-r2.lean (Finset.mem_Icc.mp of the stand-in)'),
    'f2_sum_add': ('Fin.sum_univ_add', 'Mathlib.Algebra.BigOperators.Fin',
                   'Lean: bridge probe (one public term)'),
    'a2_map_sum': ('Fin.sum_univ_add', 'Mathlib.Algebra.BigOperators.Fin',
                   'Lean: bridge probe (one public term)'),
    'f2_catalogPair_inverse': ('Turing.eq_pairEncode_of_pairDecode', 'Encoding',
                               'Lean: bridge probe (one public term, binders reordered)'),
    'f2_loop_input_run_le': ('Turing.MultiTapeTM.timed_input_bound', 'Deterministic',
                             'Lean: bridge probe (one public term)'),
}
DUP_MOD = {'Finite (MIG-0b)': T + 'TuringMachine.Finite', 'Encoding': MODS['Encoding'],
           'Deterministic': T + 'TuringMachine.Deterministic',
           'Mathlib.Algebra.BigOperators.Fin': 'Mathlib.Algebra.BigOperators.Fin'}

out = []
pop = [r for r in rows if r['fate'].startswith('move') or r['fate'].startswith('absorbed')]
for r in pop:
    home, carried = receiving(r)
    for u in r['uses']:
        q = by[u]
        f = q['fate']
        cls, retarget, where, acc, ev = '', '', '', '', ''
        if not carried:
            cls, ev = 'NOT-CARRIED', 'the citer\'s proof is replaced over the named witnesses'
            retarget = q.get('new_name') or (q['source'] or '').split(':')[-1] or u
            where, acc = '-', '-'
        elif f.startswith('move'):
            if f.startswith('move (statement'):
                retarget, qhome = u, 'Simulation'
            elif f.startswith('move: replaces'):
                retarget, qhome = 'loopHost_contracts', 'Loop'
            else:
                retarget, qhome = moved[u], HOME_OF_PATH[q['detail'].split(' (')[0]]
            priv = q['private']
            where = qhome + (' (private)' if priv else ' (public)')
            same = qhome == home
            acc = 'yes' if same or (not priv and MODS[qhome] in clos[home]) else 'NO'
            cls = 'MOVES-WITH' if same else 'IDENTICAL'
            ev = 'the same declaration text, renamed by the moved-name map'
            if f.startswith('move: replaces'):
                cls = 'GENERALIZATION'
                ev = ('the moved contract, ∃ c removed and c ↦ 10: '
                      'Lean, checks/RetargetChecks-r2.lean (⟨10, loopHost_contracts …⟩)')
        elif f.startswith('delete: duplicates'):
            retarget, dmod, ev = DUP[u]
            where = dmod + ' (public)'
            cond = ''
            if dmod.startswith('Mathlib.Algebra.BigOperators.Fin'):
                ok = dmod in clos[home] or MODS['Simulation'] in clos[home] or home == 'Simulation'
                cond = ' after F-A\'s import in Simulation (decision 4)'
            else:
                ok = DUP_MOD[dmod] in clos[home]
            acc = ('yes' + cond) if ok else 'NO'
            cls = 'GENERALIZATION' if u == 'f2_head_steps' else 'IDENTICAL'
            if u == 'f2_catalogPair_inverse':
                cls = 'GENERALIZATION'
        elif f.startswith('absorbed'):
            gate = q['detail'].split(' (')[0].split('.')[-1]
            retarget = q['detail'].split(' (')[0]
            gs, gp = unit_stmt(gate)
            ghome = q['detail'].split('(')[1].split(';')[0].strip()
            where = ghome + (' (private)' if gp else ' (public)')
            acc = 'yes' if ghome == home or MODS[ghome] in clos[home] else 'NO'
            cs = copy_stmt(u)
            cls = 'IDENTICAL' if body_stmt(cs)[1] == body_stmt(gs)[1] else 'DIFFERS'
            ev = 'gated statement in the unit'
        elif q.get('source'):
            k, ln, base = q['source'].split(':')
            hs, hp, _ = home_stmt(k, line=int(ln))
            retarget = base
            where = k + (' (private)' if hp else ' (public)')
            acc = 'yes' if k == home or (not hp and MODS[k] in clos[home]) else 'NO'
            cs = copy_stmt(u)
            same = body_stmt(cs) == body_stmt(hs)
            if q.get('code_identical'):
                cls, ev = ('IDENTICAL', 'code-identical copy') if same else ('PROBLEM', 'code '
                                                                            'identical, statement not')
            elif same:
                cls, ev = 'IDENTICAL', 'statement-identical copy (proof differs)'
            elif u in checked:
                cls = 'GENERALIZATION'
                ev = 'Lean, checks/RetargetChecks-r2.lean: ' + checked[u]
                if u == 'f2_loopHost_prepare':
                    cls = 'WEAKER at the tip; GENERALIZATION after the round-2 repair'
                    ev += ('; the same example fails against the tip\'s Loop '
                           '(checks/RetargetChecks-tip.lean)')
            elif u == 'f2_loopHost':
                cls = 'GENERALIZATION'
                ev = ('definition: f2_loopHost body F anchor findMode = '
                      'loopHostM body F anchor false findMode by rfl (bridge probe)')
            else:
                cls, ev = 'DIFFERS', 'unclassified'
        elif q['family'] == 'public':
            retarget, where = u, 'Catalog (public)'
            acc = 'yes' if home == 'Catalog' else 'NO'
            cls, ev = 'PROBLEM', 'a Catalog row cited from a lower home'
        else:
            cls, ev = 'PROBLEM', 'cited name is deleted without a retarget: ' + f
        out.append([r['name'], r['fate'].split(' (')[0][:40], home, 'yes' if carried else 'no', u,
                    f[:60], retarget, where, cls, acc, ev])

with open(OUT, 'w', encoding='utf-8') as fh:
    fh.write('citer\tciter fate\treceiving home\tproof carried\tcited\tcited fate (round 2)\t'
             'retarget\tretarget home\tstatement class\taccessible\tevidence\n')
    for o in out:
        fh.write('\t'.join(o) + '\n')
from collections import Counter  # noqa: E402
print(f'population: {len(pop)} declarations ({Counter(r["fate"].split(":")[0].split(" (")[0] for r in pop)});'
      f' citations: {len(out)}')
print('classes:', dict(Counter(o[8] for o in out)))
print('accessible:', dict(Counter(o[9] for o in out)))
print('carried citations by class:', dict(Counter(o[8] for o in out if o[3] == 'yes')))
for o in out:
    if o[8] not in ('IDENTICAL', 'MOVES-WITH') or o[9] not in ('yes', '-'):
        print(' | '.join(o[i] for i in (0, 2, 3, 4, 6, 7, 8, 9)), '|', o[10][:90])
