"""Prepare exact source archives and bounded strict copies; no library edits."""
from pathlib import Path
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
helper = (ROOT / 'devtools/seyoon/declfreeze.py').read_text()
assert helper.count('a = chunks(') == 1
ns = {}
exec(compile(helper.split('a = chunks(')[0], 'declfreeze-helper-functions', 'exec'), ns)
source = (OUT / 'Catalog-current.lean.txt').read_text()
base = (OUT / 'Catalog-base1160.lean.txt').read_text()
A = {n: (p, t) for n, p, t in ns['chunks'](base)}
B = {n: (p, t) for n, p, t in ns['chunks'](source)}


def code(t):
    return t.split('-/', 1)[1].lstrip() if t.startswith('/--') else t


defs = json.loads((ROOT / 'campaign/fills/mig1/landing/review-certshell/seal-inventory.json').read_text())['definitions'][:19]
defs += ['Turing.Cfg.ofWords', 'Turing.Cfg.mapState', 'Turing.incFixed',
         'Turing.pairEncode', 'Turing.pairDecode', 'Turing.splitAtLastTrue', 'Turing.solveSplit',
         'Turing.stateWord', 'Turing.pairDiagTM',
         'Turing.FinTM.idTM', 'Turing.FinTM.constTM', 'Turing.FinTM.prependTM',
         'Turing.FinTM.lengthBitsTM', 'Turing.FinTM.polyUnaryTM', 'Turing.FinTM.polyBitsTM',
         'Turing.FinTM.pairExtractTM', 'Turing.FinTM.pairValidTM', 'Turing.FinTM.pairLenCheckTM',
         'Turing.FinTM.stripLastTM', 'Turing.FinTM.incFixedTM', 'Turing.FinTM.pairMapSndTM',
         'Turing.FinTM.splitSolveTM', 'Turing.FinTM.redirectTM', 'Turing.FinTM.timedCondTM',
         'Turing.FinTM.branchTM']
assert len(defs) == len(set(defs)) == 44
off = 'attribute [-simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
on = 'attribute [simp] Turing.Action.apply Turing.Cfg.init Turing.MultiTapeTM.initCfg\n'
guard = 'attribute [local irreducible] ' + ' '.join(defs) + '\n' + off
(OUT / 'guard44.txt').write_text(guard)
hold = {'Turing.FinTM.computesFunInTime_pairDup_spaceUsed',
        'Turing.FinTM.computesFunInTime_incFixed_spaceUsed'}
changed = [n for n in B if n not in A or (B[n][1] != A[n][1] and code(B[n][1]).split(':=', 1)[1] != code(A[n][1]).split(':=', 1)[1])]
assert len(changed) == 27 and hold <= set(changed)
doconly = [n for n in B if n in A and B[n][1] != A[n][1] and n not in changed]
assert len(doconly) == 4
spans = []
for n in changed:
    chunk = B[n][1]
    assert source.count(chunk) == 1, n
    lo = source.index(chunk)
    spans.append(dict(name=n, start=lo, end=lo + len(chunk),
                      line=source.count('\n', 0, lo) + 1, hold=n in hold))


def prepare(name, names):
    inserts = []
    pieces = []
    for i, s in enumerate(x for x in spans if x['name'] in names):
        tag = f'CatalogReview{i + 1:02d}'
        before = f'section {tag}\n' + guard
        after = '\n#print axioms ' + s['name'] + '\n' + on + f'end {tag}\n'
        inserts += [(s['start'], before), (s['end'], after)]
        pieces += [before, after]
    text = source
    for pos, value in sorted(inserts, key=lambda x: x[0], reverse=True):
        text = text[:pos] + value + text[pos:]
    restored = text
    for piece in pieces:
        assert restored.count(piece) == 1
        restored = restored.replace(piece, '', 1)
    assert restored == source
    (OUT / (name + '.lean.txt')).write_text(text)
    return dict(input=name, names=sorted(names), inserted_pieces=pieces,
                restored_sha256=hashlib.sha256(restored.encode()).hexdigest(),
                guarded_sha256=hashlib.sha256(text.encode()).hexdigest())


passing = prepare('Catalog-strict-v1', set(changed) - hold)
pending = prepare('Catalog-pending-strict-v1', hold)
public_a = {n for n in A if not A[n][0]}
public_b = {n for n in B if not B[n][0]}
assert not public_b - public_a
assert public_a - public_b == {'Turing.' + n for n in [
    'transferTM_run', 'copyTM_run', 'clearTM_run', 'compareTM_run',
    'incrementTM_run_succ', 'incrementTM_run_overflow']}
for n in A.keys() & B.keys():
    assert code(A[n][1]).split(':=', 1)[0] == code(B[n][1]).split(':=', 1)[0], n
    if not re.search(r'\b(theorem|lemma)\b', code(B[n][1]).split(':=', 1)[0]):
        assert A[n][1] == B[n][1], n
base_imports = re.findall(r'^import .*', base, re.M)
current_imports = re.findall(r'^import .*', source, re.M)
expected_imports = base_imports[:3] + ['import TCSlib.Complexity.TuringMachine.Build.Primitives'] + base_imports[3:]
assert current_imports == expected_imports
inv = dict(definitions=defs, count=44, guarded_changed_proofs=25, pending_rows=sorted(hold),
           changed_proof_spans=spans, doc_only_with_byte_identical_proofs=doconly,
           source_restoration=[passing, pending],
           exceptions=['loopHostTM is a reducible abbrev, not an ordinary def; structure fields and Core/Mathlib reduction follow standing rules.'],
           unchanged_legacy_helpers_outside_guards=True, guard_before_docstrings_and_headers=True,
           default_simp_disabled=['Turing.Action.apply', 'Turing.Cfg.init', 'Turing.MultiTapeTM.initCfg'],
           public_counts=[len(public_a), len(public_b)], private_counts=[len(A)-len(public_a), len(B)-len(public_b)],
           public_removed=sorted(public_a-public_b), private_removed=sum(A[n][0] for n in A if n not in B),
           private_added=[n for n in B if n not in A], all_retained_headers_literal_equal=True,
           all_retained_definition_table_bodies_literal_equal=True, imports_literal_equal=False, imports_exact_authorized_addition='TCSlib.Complexity.TuringMachine.Build.Primitives (megafill brief lines94–97)')
(OUT / 'seal-inventory.json').write_text(json.dumps(inv, indent=2) + '\n')
print(json.dumps({k: inv[k] for k in ['count','guarded_changed_proofs','pending_rows','doc_only_with_byte_identical_proofs','public_counts','private_counts','private_removed','private_added']}, indent=2))
