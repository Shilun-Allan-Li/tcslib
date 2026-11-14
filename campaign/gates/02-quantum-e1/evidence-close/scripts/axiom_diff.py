"""Compare two axiom censuses (Axioms.lean output: one row per non-internal constant of the
audited modules, i.e. constants whose names `Name.isInternal` does not flag) by constant name,
and classify the additions and removals by kind (E1 epoch audit, finding 9).
Usage: python3 -I axiom_diff.py <old axioms.log> <new axioms.log>"""
import sys, re
def load(p):
    rows = {}
    for line in open(p, encoding='utf-8'):
        parts = line.rstrip('\n').split('\t')
        if len(parts) == 5: rows[parts[3]] = (parts[0], parts[1], parts[2])
    return rows
def kind(name, k):
    last = name.split('.')[-1]
    if re.fullmatch(r'eq_\d+|eq_def', last): return 'generated equation lemma'
    if re.fullmatch(r'match_\d+(_\d+)?', last): return 'matcher'
    if last == 'congr_simp': return 'congr_simp lemma'
    if re.fullmatch(r'(proof|_proof)_\d+', last): return 'auxiliary proof'
    return f'source {k}'
old, new = load(sys.argv[1]), load(sys.argv[2])
print(f'old: {len(old)} constants; new: {len(new)} constants')
for label, names in (('ADDED', sorted(set(new) - set(old))), ('REMOVED', sorted(set(old) - set(new)))):
    by = {}
    for n in names:
        r = new.get(n) or old.get(n); by.setdefault(kind(n, r[1]), []).append((n, r[0]))
    print(f'{label}: {len(names)}')
    for k in sorted(by):
        print(f'  {k}: {len(by[k])}')
        for n, tag in by[k]: print(f'    {tag}  {n}')
changed = sorted(n for n in set(old) & set(new) if old[n][0] != new[n][0])
print(f'CARRIED OVER: {len(set(old) & set(new))}; tag changed (SORRY <-> CLEAN): {len(changed)}')
