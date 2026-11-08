"""Independent read-only validation of PFR data; never import/execute its tools."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

PREP = Path('/Users/seyoonr/.codex/worktrees/ps-gate06-integration/tcslib-pass-shelat-ch2-4/.lake/ps-maintainer/cleanup-part2-prep')
MAIN = Path('/Users/seyoonr/phd_experiments/tcslib_all_branches/tcslib-pass-shelat-ch2-4')
SUP = PREP / 'external-bootstrap-r1'
OUT = Path('/private/tmp/cleanup-pfr-review-r1-20261107')


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def mask(text):
    """Mask nested Lean comments and string literals while retaining line offsets."""
    result = []
    i = depth = 0
    while i < len(text):
        if depth:
            if text.startswith('/-', i):
                depth += 1; result.extend('  '); i += 2
            elif text.startswith('-/', i):
                depth -= 1; result.extend('  '); i += 2
            else:
                result.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('/-', i):
            depth = 1; result.extend('  '); i += 2
        elif text.startswith('--', i):
            end = text.find('\n', i)
            if end < 0: end = len(text)
            result.extend(' ' * (end - i)); i = end
        elif text[i] == '"':
            result.append(' '); i += 1
            while i < len(text):
                char = text[i]; result.append('\n' if char == '\n' else ' '); i += 1
                if char == '\\' and i < len(text):
                    result.append('\n' if text[i] == '\n' else ' '); i += 1
                elif char == '"':
                    break
        else:
            result.append(text[i]); i += 1
    assert depth == 0
    return ''.join(result)


def imports(text):
    rows = []
    for line_no, line in enumerate(mask(text).splitlines(), 1):
        match = re.match(r'^\s*import\s+(.+?)\s*$', line)
        if match:
            for name in match.group(1).split():
                assert re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*', name), name
                rows.append({'line': line_no, 'module': name})
    return rows


def check_manifest(directory, filename, key):
    data = json.loads((directory / filename).read_text())
    for row in data[key]:
        raw = (directory / row['path']).read_bytes()
        assert len(raw) == row['bytes'] and sha(raw) == row['sha256'], row['path']
    return len(data[key])


delivery = SUP / 'DELIVERY-MANIFEST.json'
assert sha(delivery.read_bytes()) == '70dd1a408a2c0c46af7ab2da50ff50520b26b2983e298492935008debb1a2cbd'
manifest_files = check_manifest(SUP, 'DELIVERY-MANIFEST.json', 'files')
check_manifest(SUP, 'MANIFEST.json', 'outputs')
manifest = json.loads((SUP / 'MANIFEST.json').read_text())
assert sha((MAIN / 'lake-manifest.json').read_bytes()) == manifest['tracked_lake_manifest_sha256']
assert sha((MAIN / 'scripts/lean_check_tree.sh').read_bytes()) == manifest['checker_sha256']

rows = json.loads((SUP / 'ordered-modules.json').read_text())
assert len(rows) == 31
modules = [row['module'] for row in rows]
assert len(set(modules)) == 31
assert len(set(row['package_relative_source'] for row in rows)) == 31
assert (SUP / 'order.txt').read_text().splitlines() == [m.replace('.', '/') for m in modules]
assert (SUP / 'bootstrap-order.txt').read_text().splitlines() == [
    '.lake/packages/PFR/' + row['package_relative_source'].removesuffix('.lean') for row in rows]
graph = json.loads((SUP / 'graph.json').read_text())
actual_edges = {}
private_sites = []
seen = set()
for ordinal, row in enumerate(rows, 1):
    assert row['ordinal'] == ordinal and row['package'] == 'PFR'
    assert row['module'].replace('.', '/') + '.lean' == row['package_relative_source']
    assert row['package_revision'] == 'e1095d58b7c6f10734988816f7764f2103b9bf29'
    package = MAIN / '.lake/packages/PFR'
    path = package / row['package_relative_source']
    raw = path.read_bytes()
    assert len(raw) == row['bytes'] and sha(raw) == row['source_sha256']
    assert git(package, 'show', row['package_revision'] + ':' + row['package_relative_source']) == raw
    blob = hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest()
    assert blob == row['git_blob']
    assert imports(raw.decode()) == row['imports'], row['module']
    actual_edges[row['module']] = [r['module'] for r in row['imports']]
    for name in actual_edges[row['module']]:
        if name.startswith('PFR.'):
            assert name in seen, (row['module'], name)
        else:
            assert name.startswith('Mathlib.'), name
    for line_no, line in enumerate(mask(raw.decode()).splitlines(), 1):
        if re.search(r'\bprivate\s+(?:noncomputable\s+)?(?:def|theorem|lemma|abbrev|instance)\b', line):
            private_sites.append({'module': row['module'], 'line': line_no, 'source_line': line.strip()})
    seen.add(row['module'])
assert graph['compile_edges'] == actual_edges
closure = set()
frontier = list(graph['roots'])
while frontier:
    name = frontier.pop()
    if name in closure: continue
    closure.add(name)
    frontier.extend(x for x in actual_edges[name] if x.startswith('PFR.'))
assert closure == set(modules)
boundary = {x for xs in actual_edges.values() for x in xs if x.startswith('Mathlib.')}
assert len(boundary) == 30
assert set((SUP / 'mathlib-direct-roots.txt').read_text().splitlines()) == boundary
boundaries = json.loads((SUP / 'boundaries.json').read_text())
assert {r['module'] for r in boundaries} == boundary
for row in boundaries:
    raw = (MAIN / '.lake/packages' / row['package'] / row['package_relative_source']).read_bytes()
    assert len(raw) == row['bytes'] and sha(raw) == row['source_sha256']
    assert git(MAIN / '.lake/packages' / row['package'], 'show', row['package_revision'] + ':' + row['package_relative_source']) == raw
    assert hashlib.sha1(b'blob ' + str(len(raw)).encode() + b'\0' + raw).hexdigest() == row['git_blob']
old = set((PREP / 'issue-inputs-r1/mathlib/all-needed-union-roots.txt').read_text().splitlines())
extra = set((SUP / 'mathlib-extra-roots.txt').read_text().splitlines())
union = set((SUP / 'mathlib-full-union-roots.txt').read_text().splitlines())
assert len(old) == 375 and extra == boundary - old and len(extra) == 14
assert union == old | boundary and len(union) == 389
plans = json.loads((SUP / 'physical-output-plan.json').read_text())
assert len(plans) == 31
for row, plan in zip(rows, plans):
    source_rel = row['package_relative_source']
    assert plan['module'] == row['module']
    assert plan['checker_rel_argument'] == '.lake/packages/PFR/' + source_rel.removesuffix('.lean')
    physical = '.lake/packages/PFR/' + source_rel.removesuffix('.lean') + '.olean'
    logical = row['module'].replace('.', '/') + '.olean'
    assert plan['expected_physical_output_relative_to_tree'] == physical
    assert plan['import_lookup_relative_to_tree'] == logical
    assert '.lake/packages/PFR/' + logical == physical

tools = {name: {'bytes': (PREP / 'external-tools-r1' / name).stat().st_size,
                'sha256': sha((PREP / 'external-tools-r1' / name).read_bytes())} for name in
         ['prepare_pfr.py', 'pfr_lean.py', 'native_validation.py', 'RUNBOOK.md', 'PFRIdentityProbe.source.txt']}
probe = (PREP / 'external-tools-r1/PFRIdentityProbe.source.txt').read_text()
expected_text = probe.split('let expected : Array Name := #[', 1)[1].split(']', 1)[0]
assert re.findall(r'`(PFR(?:\.[A-Za-z0-9_]+)+)', expected_text) == modules
assert 'env.getModuleIdx? m' in probe and 'actual == m' in probe
assert 'env.getModuleIdxFor? n' in probe and 'actual == wanted' in probe
assert '"_private." ++ home.toString ++ "."' in probe
drafts = {name: sha((PREP / 'issue-draft-r2' / name).read_bytes()) for name in
          ['brief.md', 'public-exceptions.md', 'REVISION-MANIFEST.json']}
result = {'kind': 'independent_static_data_validation_only', 'native_performed': False,
          'delivered_tools_imported_or_executed': False, 'supplement_manifest_sha256': sha(delivery.read_bytes()),
          'supplement_files_verified': manifest_files, 'pfr_modules': 31, 'pfr_source_git_blobs_exact': 31,
          'source_import_records_exact': True, 'transitive_root_closure_exact': True,
          'topological_order_exact': True, 'mathlib_boundaries_git_blobs_exact': 30,
          'old_mathlib_roots': len(old), 'extra_mathlib_roots': len(extra), 'full_union_roots': len(union),
          'physical_logical_object_mapping_exact': True, 'explicit_private_sites': private_sites,
          'probe_expected_modules_exact': True,
          'tool_sha256': tools, 'candidate_r2_sha256': drafts,
          'checker_sha256': manifest['checker_sha256']}
(OUT / 'static-validation.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k != 'explicit_private_sites'}, indent=2))
print('explicit_private_sites', len(private_sites))
