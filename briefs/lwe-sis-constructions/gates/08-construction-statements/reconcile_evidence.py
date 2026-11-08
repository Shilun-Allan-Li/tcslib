"""Reconcile the combined statement gate; this performs no native check or dispatch."""

from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import runpy
import subprocess
import sys


HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
E = HERE / 'evidence'
BASE = '307cfdd1d6cadfda2ae9cca5367705ad770c5f42'
CENTRAL = '2c37f3f486822a52f4a9e337c6b742e995ebb118'
FINAL = 'audit-final-sweep'
INSPECT = runpy.run_path(str(HERE / 'statement_census.py'))['inspect']
EXPORTS = {'TCSlib.lean', 'TCSlib/Cryptography/Encoding.lean',
    'TCSlib/Cryptography/LWE.lean', 'TCSlib/Cryptography/Encryption.lean',
    'TCSlib/Cryptography/Hashing/SIS.lean', 'TCSlib/Cryptography/Pseudorandom.lean'}
SCOPES = ['Encoding', 'LWE', 'SIS', 'Encryption/Symmetric/Regev',
    'Encryption/PublicKey/Regev', 'Hashing/SIS', 'Pseudorandom/Generators/LWE',
    'TrapdoorFunctions']


def write(name, value):
    (E / name).write_text(json.dumps(value, indent=2) + '\n')


def git(*args, data=None):
    return subprocess.check_output(['git', *args], cwd=ROOT, input=data)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    pin = None if '--precommit' in sys.argv else (E / 'source-pin.txt').read_text().strip()
    modules = json.loads((E / 'new-math-modules.json').read_text())
    rows, closed = [], set()
    for module in modules:
        _, declarations, proofs = INSPECT((ROOT / (module + '.lean')).read_text())
        for kind, name in declarations:
            admitted = bool(re.search(r'\bsorry\b', proofs.get(name, '')))
            rows.append(dict(module=module, kind=kind, name=name, directly_admitted=admitted))
            if name in proofs and not admitted:
                assert proofs[name] == 'rfl', (name, proofs[name])
                closed.add(name)
    assert len(modules) == 19 and len(rows) == 220
    assert Counter(x['kind'] for x in rows) == {'def': 57, 'theorem': 163}
    assert sum(x['directly_admitted'] for x in rows) == 101 and len(closed) == 62
    source_names = {x['name'] for x in rows}
    def_names = {x['name'] for x in rows if x['kind'] == 'def'}

    probe = json.loads((E / 'axiom-probe/checks.json').read_text())
    assert len(probe) == 1 and probe[0]['exit_code'] == probe[0]['error_lines'] == 0
    assert probe[0]['fresh_olean']
    raw = (ROOT / probe[0]['log']).read_text()
    printed = {}
    for match in re.finditer(
        r"'([^']+)' depends on axioms:\s*\[(.*?)\]|'([^']+)' does not depend on any axioms",
        raw, re.S):
        printed[match[1] or match[3]] = [] if match[3] else sorted(
            x.strip() for x in match[2].split(',') if x.strip())
    backing = json.loads((E / 'backing-contracts.json').read_text())
    assert set(printed) == source_names | set(backing)
    standard = {'propext', 'Classical.choice', 'Quot.sound'}
    assert all(set(printed[n]) <= standard for n in backing)
    write('backing-contract-axioms.json', [dict(name=n, axioms=printed[n]) for n in backing])

    baseline = {x['name']: x for x in json.loads((ROOT /
        'briefs/lwe-sis-constructions/fills/03-dyadic-arithmetic/evidence/elaborated-constants.json').read_text())}
    constants, axioms = [], {}
    for line in raw.splitlines():
        if line.startswith('COMBINED_CONSTANT|'):
            _, module, name, kind, private = line.split('|')
            constants.append(dict(module=module, name=name, kind=kind, private=private == 'true'))
        if line.startswith('COMBINED_AXIOMS|'):
            _, name, labels = line.split('|')
            axioms[name] = sorted(filter(None, labels.split(',')))
    assert len(baseline) == 302 and set(baseline) <= set(axioms)
    assert len(constants) == len({x['name'] for x in constants}) == len(axioms)
    generated, auxiliaries = [], []
    for row in constants:
        n = row['name']; row['axioms'] = axioms[n]
        assert not row['private'] and row['kind'] != 'axiom', row
        assert set(row['axioms']) <= standard | {'sorryAx'}, row
        if n in baseline:
            assert all(row[k] == baseline[n][k] for k in ['module', 'kind', 'private', 'axioms']), row
            row['category'] = 'unchanged audited constant'
        elif n in source_names:
            row['category'] = 'source declaration'
        elif '._proof_' in n or '.congr_simp' in n or '._simp_' in n:
            row['category'] = 'compiler auxiliary'; auxiliaries.append(row)
        else:
            assert row['kind'] == 'theorem' and any(n.startswith(d + '_') for d in def_names), row
            row['category'] = 'generated non-simp projection reader'; generated.append(row)
        if n not in source_names:
            assert set(row['axioms']) <= standard, row
    for row in rows:
        row['axioms'] = printed[row['name']]
        assert row['axioms'] == axioms[row['name']]
        assert ('sorryAx' in row['axioms']) == row['directly_admitted'], row
    assert len(constants) == 575 and len(generated) == 40 and len(auxiliaries) == 13
    write('source-declarations.json', rows)
    write('admissions.json', [x for x in rows if x['directly_admitted']])
    write('elaborated-constants.json', sorted(constants, key=lambda x: x['name']))
    write('generated-projection-readers.json', sorted(generated, key=lambda x: x['name']))
    write('new-compiler-constants.json', sorted(auxiliaries, key=lambda x: x['name']))

    order = (E / 'module-order.txt').read_text().splitlines()
    sweep = json.loads((E / FINAL / 'checks.json').read_text())
    assert len(sweep) == len(order) == 144 and [x['module'] for x in sweep] == order
    warnings = Counter()
    for row in sweep:
        assert row['exit_code'] == row['error_lines'] == 0 and row['fresh_olean'], row
        data = (ROOT / (row['module'] + '.lean')).read_bytes()
        snapshot = E / FINAL / 'source-snapshots' / (row['module'] + '.lean')
        assert data == snapshot.read_bytes() and sha(data) == row['source_sha256']
        log = (ROOT / row['log']).read_text()
        assert not re.search(r'\berror(?:\([^)]*\))?:', log)
        assert row['admission_warnings'] == log.count("declaration uses 'sorry'")
        warnings['new' if row['module'] in modules else 'inherited'] += row['admission_warnings']
    assert warnings == {'new': 101, 'inherited': 17}, warnings

    # Check the complete library tree, including old modules outside this sweep.
    old = {}
    for line in git('ls-tree', '-r', BASE, '--', 'TCSlib', 'TCSlib.lean').decode().splitlines():
        info, path = line.split('\t', 1)
        if path.endswith('.lean'):
            old[path] = info.split()[2]
    current = {str(p.relative_to(ROOT)) for p in (ROOT / 'TCSlib').rglob('*.lean')} | {'TCSlib.lean'}
    assert set(old) <= current
    paths = sorted(old)
    hashes = git('hash-object', '--stdin-paths', data=('\n'.join(paths) + '\n').encode()).decode().splitlines()
    modified = {p for p, h in zip(paths, hashes) if h != old[p]}
    assert modified == EXPORTS, modified
    added = sorted(current - set(old)); assert len(added) == 25
    assert set(m + '.lean' for m in modules) <= set(added)
    write('invariance.json', dict(baseline=BASE, original_library_lean_paths=len(old),
        unchanged_library_lean_paths=len(old) - len(modified),
        modified_existing_lean_paths=sorted(modified), added_lean_paths=added,
        removed_lean_paths=[], existing_definition_or_theorem_edited=False,
        shared_owner_api_or_registry_edited=False, new_hosts=0,
        copied_existing_proved_infrastructure=0, export_commit_separate=True))
    control = ['TCSlib.lean', 'lean-toolchain', 'lake-manifest.json', 'AGENTS.md',
        'policy.md', 'workflow.md', 'machine-library-design.md',
        'scripts/lean_check_tree.sh', 'scripts/campaign_style_lint.py']
    source_paths = sorted(set([m + '.lean' for m in order] + control))
    files = []
    for path in source_paths:
        data = (ROOT / path).read_bytes()
        if pin:
            assert data == git('show', pin + ':' + path), path
        if path not in EXPORTS and path not in added:
            assert data == git('show', BASE + ':' + path), path
        files.append(dict(path=path, bytes=len(data), sha256=sha(data)))
    write('source-freeze.json', dict(source_pin=pin, baseline=BASE,
        remote_verified_central_base=CENTRAL, files=files))

    style_counts = []
    for scope in SCOPES:
        result = subprocess.run([sys.executable, '-I', 'scripts/campaign_style_lint.py',
            'TCSlib/Cryptography/' + scope], cwd=ROOT, capture_output=True, text=True)
        (E / ('style-' + scope.replace('/', '-') + '.log')).write_text(result.stdout + result.stderr)
        match = re.search(r'style_lint: (\d+) FAIL, (\d+) WARN over (\d+) files', result.stdout)
        assert result.returncode == 0 and match
        style_counts.append(tuple(map(int, match.groups())))
    style = tuple(map(sum, zip(*style_counts)))
    assert style == (0, 2, 41), style
    reports = []
    for p in sorted((ROOT / 'audits').glob('lwe-sis-*-findings.md')):
        data = p.read_bytes(); assert data == git('show', BASE + ':' + str(p.relative_to(ROOT)))
        reports.append(dict(path=str(p.relative_to(ROOT)), bytes=len(data), sha256=sha(data)))
    assert len(reports) == 8
    write('prior-findings.json', reports)
    summary = dict(source_pin=pin, baseline=BASE, remote_verified_central_base=CENTRAL,
        branch='cryptography/lwe-sis-construction-statements', central_target='cryptography/lwe-sis-constructions',
        dependency_prs=[236, 237, 238, 239], mathematical_modules=19, source_declarations=220,
        definitions=57, theorems=163, closed_source_rfl_readers=62, direct_admissions=101,
        earlier_owned_constants=302, total_owned_constants=len(constants),
        generated_non_simp_projection_readers=len(generated), new_compiler_auxiliaries=len(auxiliaries),
        owned_constants_with_sorryAx=101, backing_contracts=len(backing),
        fresh_modules=144, fresh_seconds=round(sum(x['seconds'] for x in sweep), 3),
        final_sweep='evidence/' + FINAL + '/checks.json',
        final_objects='.lake/construction-audit-final-oleans',
        admission_warnings=dict(warnings), axiom_probe_seconds=probe[0]['seconds'],
        source_freeze_files=len(files), style_failures=style[0], style_warnings=style[1],
        style_files=style[2], prior_scoped_audits_pass=8, shared_proposals_applied=False,
        whole_library_root_checked=False, external_statement_audit_closed=False,
        source_policy_closed=False, merge_approval_claimed=False, native_or_cache_pids_killed=[])
    write('summary.json', summary)
    print(json.dumps(summary, indent=2))


if __name__ == '__main__':
    main()
