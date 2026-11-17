"""targets.py <tree> : the sorry'd targets of the six fill units at the synthetic base, as TSV
unit, row, path:line (header line), full name.  Namespaces resolved from namespace/end lines;
the row is the first **C17.**/**N7.**/**F5,** marker of the declaration's docstring."""
import re, sys, os
root = sys.argv[1]
U = [('U4','TCSlib/Complexity/BranchingPrograms/BarringtonConverse.lean'),
     ('U5','TCSlib/Complexity/BranchingPrograms/NC1.lean'),
     ('U7','TCSlib/Complexity/CircuitComplexity/NANDLayering.lean'),
     ('U9','TCSlib/Complexity/CircuitComplexity/FormulaArith/CarrySave.lean'),
     ('U10','TCSlib/Complexity/CircuitComplexity/FormulaArith/Compare.lean'),
     ('U11','TCSlib/Complexity/CircuitComplexity/FormulaArith/ModSum.lean')]
print('unit\trow\tfile:line\tdeclaration')
tot = 0
for u, p in U:
    L = open(os.path.join(root, p)).read().split('\n')
    ns, doc, cur = [], [], None
    for i, l in enumerate(L, 1):
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1] == m.group(1): ns.pop(); continue
        if l.startswith('/--'): doc = [l]; continue
        if doc and not doc[-1].rstrip().endswith('-/') : doc.append(l); continue
        m = re.match(r'^(?:private\s+)?theorem\s+(\S+)', l)
        if m:
            row = re.search(r'\*\*([CNF]\d+)[.,]', ' '.join(doc))
            cur = (row.group(1) if row else '?', i, '.'.join(ns + [m.group(1)]))
            doc = []
            continue
        if re.match(r'^\s+sorry\s*$', l) and cur:
            print(f'{u}\t{cur[0]}\t{p}:{cur[1]}\t{cur[2]}'); tot += 1; cur = None
print(f'# TOTAL {tot}')
