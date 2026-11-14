"""Source-only inventory, dependency order, root census and duplication searches."""
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

root, evidence = Path(sys.argv[1]), Path(sys.argv[2])
prefix = 'TCSlib/Cryptography/Authentication/Signatures/Lamport'
names = ['Machine', 'Seed', 'Closing', 'Blocks', 'MachineSpec', 'Advice', 'Nonabort',
         'InversionProbability', 'Realization']
targets = {prefix + '/' + name for name in names}
seen, order, roots = set(), [], set()


def visit(module):
    if module in seen:
        return
    seen.add(module)
    source = root / (module + '.lean')
    if not source.exists():
        raise RuntimeError('missing import source: ' + module)
    for line in source.read_text().splitlines():
        if line.startswith('import '):
            for dep in line.split()[1:]:
                if dep.startswith('TCSlib.'):
                    visit(dep.replace('.', '/'))
                elif dep.startswith('Mathlib.'):
                    roots.add(dep)
    order.append(module)


for module in sorted(targets):
    visit(module)
issued = set((evidence / 'inputs/order.txt').read_text().splitlines())
t1 = set((evidence / 'inputs/t1-extra-order.txt').read_text().splitlines())
existing_helpers = {prefix + '/' + p.stem for p in (root / prefix).glob('*.lean')} - targets
needed = [m for m in order if m in targets or m not in issued | t1 | existing_helpers]
issued_roots = set((evidence / 'inputs/roots.txt').read_text().splitlines())
(evidence / 'inputs/final-machine-helper-order.txt').write_text('\n'.join(needed) + '\n')

records = []
for name in names:
    path = root / prefix / (name + '.lean')
    text = path.read_text()
    lines = text.splitlines()
    required = ['Copyright', 'import ', 'set_option maxHeartbeats 0',
                'set_option relaxedAutoImplicit false', 'set_option autoImplicit false',
                '# ', '## Main definitions', '## Main results', '## References']
    missing = [field for field in required if field not in text]
    declarations = [(i, line) for i, line in enumerate(lines, 1)
                    if re.match(r'^(?:noncomputable )?(?:def|abbrev|theorem|lemma)\b', line)]
    undocumented = []
    for i, line in declarations:
        preceding = '\n'.join(lines[:i - 1]).rstrip()
        if not preceding.endswith('-/'):
            undocumented.append(dict(line=i, declaration=line))
    record = dict(file=str(path.relative_to(root)), lines=len(lines),
                  sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                  missing_header_fields=missing, undocumented_public_declarations=undocumented,
                  declarations=declarations)
    records.append(record)
    assert len(lines) < 1000 and not missing and not undocumented, record
result = dict(records=records, new_mathlib_roots=sorted(roots - issued_roots),
              all_closure_mathlib_roots=sorted(roots),
              new_foreign_prerequisites=[m for m in needed if m not in targets],
              exact_foreign_definition_reader_review='manual, documented in final-machine-helper-audit.md',
              compiler_run=False)
(evidence / 'inputs/final-machine-helper-static-audit.json').write_text(json.dumps(result, indent=2) + '\n')

searches = [
    ['rg', '-n', 'tmsat_pt_take', 'TCSlib/Complexity/ClassNP/TMSAT.lean'],
    ['rg', '-n', 'clA5Drop_native', 'TCSlib/Complexity/CookLevin/Hardness.lean'],
    ['rg', '-n', 'flatten.*Function.update|Function.update.*flatten', 'TCSlib'],
    ['rg', '-n', 'headD_drop_ofFn|publicWord_flatten|indexBits_value|exists_withIndexAdvice', 'TCSlib'],
    ['rg', '-n', "sorry|admit|^axiom|unsafe|@\\[simp", *[prefix + '/' + name + '.lean' for name in names]],
]
with (evidence / 'logs/final-machine-helper-searches.log').open('w') as log:
    for command in searches:
        log.write('$ ' + ' '.join(command) + '\n')
        log.flush()
        p = subprocess.run(command, cwd=root, stdout=log, stderr=subprocess.STDOUT)
        log.write(f'EXIT {p.returncode}\n\n')
print(json.dumps(dict(files=len(records), all_below_1000=True, headers_and_docstrings='PASS',
                     new_mathlib_roots=result['new_mathlib_roots'],
                     new_foreign_prerequisites=result['new_foreign_prerequisites'],
                     compiler_run=False), indent=2))
