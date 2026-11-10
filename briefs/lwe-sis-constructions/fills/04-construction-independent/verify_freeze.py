"""Verify proof-only changes against the passed statement gate plus its doc repair.

Reuse the campaign comment/command scanner. Select the first outer assignment
followed by `by` or `rfl`: statement types may have outer lets, while proof bodies
may themselves have later assignments. Historical statement tooling is unchanged.
"""

import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
SETUP = json.loads((HERE / 'setup.json').read_text())
BASE = SETUP['proof_baseline']
OLD = ROOT / 'briefs/lwe-sis-constructions/gates/08-construction-statements'
SCANNER = runpy.run_path(str(OLD / 'statement_census.py'))
STRIP, COMMAND, DECL = (SCANNER[n] for n in ['STRIP', 'COMMAND', 'DECL'])


def git(*args, data=None):
    return subprocess.check_output(['git', *args], cwd=ROOT, input=data)


def inspect(source):
    text = STRIP(source)
    starts = list(COMMAND.finditer(text))
    output, declarations, proofs, namespaces = [], [], {}, []
    output.append(text[:starts[0].start()] if starts else text)
    for index, start in enumerate(starts):
        stop = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        block = text[start.start():stop]
        first = block.splitlines()[0]
        if first.startswith('namespace '):
            namespaces.append(first.split()[1])
        elif first == 'end' or first.startswith('end '):
            namespaces.pop()
        match = DECL.match(first)
        if match:
            kind, tail = match.groups()
            name = re.match(r'[^\s(:{]+', tail).group(0)
            full = '.'.join([*namespaces, name])
            declarations.append((kind, full))
            if kind in {'theorem', 'lemma'}:
                stack, offset = [], None
                pairs = {'(': ')', '[': ']', '{': '}'}
                for pos, char in enumerate(block):
                    if char in pairs:
                        stack.append(pairs[char])
                    elif stack and char == stack[-1]:
                        stack.pop()
                    elif not stack and block.startswith(':=', pos):
                        if re.match(r'\s*(?:by\b|rfl\b)', block[pos + 2:]):
                            offset = pos
                            break
                assert offset is not None, full
                proofs[full] = ' '.join(block[offset + 2:].split())
                block = block[:offset + 2] + ' <proof>\n'
        output.append(block)
    return ' '.join(''.join(output).split()), declarations, proofs


def main():
    modules = json.loads((OLD / 'evidence/new-math-modules.json').read_text())
    changed, targets, count = [], [], 0
    for module in modules:
        path = module + '.lean'
        before = git('show', BASE + ':' + path).decode()
        after = (ROOT / path).read_text()
        a, ds, ps = inspect(before)
        b, dt, pt = inspect(after)
        assert a == b and ds == dt and ps.keys() == pt.keys(), path
        count += len(ds)
        for name in ps:
            if ps[name] != 'by sorry':
                assert ps[name] == pt[name], ('Closed reader changed', name)
            else:
                admitted = bool(re.search(r'\bsorry\b', pt[name]))
                targets.append(dict(module=module, name=name, directly_admitted=admitted,
                    original_proof_sha256=hashlib.sha256(ps[name].encode()).hexdigest(),
                    current_proof_sha256=hashlib.sha256(pt[name].encode()).hexdigest()))
            if ps[name] != pt[name]:
                assert ps[name] == 'by sorry', name
                changed.append(name)
    assert count == 220 and len(targets) == 101
    paths = sorted(x['path'] for x in json.loads((OLD / 'evidence/source-freeze.json').read_text())['files'])
    owned = {m + '.lean' for m in modules}
    for path in paths:
        if path not in owned:
            assert (ROOT / path).read_bytes() == git('show', BASE + ':' + path), path
    tree = {}
    for line in git('ls-tree', '-r', BASE, '--', 'TCSlib', 'TCSlib.lean').decode().splitlines():
        info, path = line.split('\t', 1)
        if path.endswith('.lean'):
            tree[path] = info.split()[2]
    current = {str(p.relative_to(ROOT)) for p in (ROOT / 'TCSlib').rglob('*.lean')} | {'TCSlib.lean'}
    assert current == tree.keys(), 'Library paths added or removed during fill.'
    hashes = git('hash-object', '--stdin-paths', data=('\n'.join(sorted(tree)) + '\n').encode()).decode().splitlines()
    modified = [p for p, h in zip(sorted(tree), hashes) if h != tree[p]]
    assert set(modified) <= owned, modified
    result = dict(statement_source=SETUP['statement_freeze'], proof_baseline=BASE,
        modules=len(modules), source_declarations=count, initial_admissions=101,
        closed_source_readers_preserved=62, changed_theorem_bodies=len(changed),
        filled_targets=sum(not x['directly_admitted'] for x in targets),
        remaining_direct_admissions=sum(x['directly_admitted'] for x in targets),
        modified_library_paths=modified, added_library_paths=[], removed_library_paths=[],
        signature_definition_import_option_attribute_namespace_changes=False,
        all_non_owned_frozen_source_paths_unchanged=True,
        elaborated_type_hash_comparison=False)
    evidence = HERE / 'evidence'
    evidence.mkdir(exist_ok=True)
    (evidence / 'freeze.json').write_text(json.dumps(result, indent=2) + '\n')
    (evidence / 'targets.json').write_text(json.dumps(targets, indent=2) + '\n')
    print(json.dumps(result, indent=2))


if __name__ == '__main__':
    main()
