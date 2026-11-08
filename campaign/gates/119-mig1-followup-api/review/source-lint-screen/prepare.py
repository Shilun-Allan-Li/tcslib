from pathlib import Path
import base64, datetime, hashlib, io, json, subprocess, tarfile, tempfile

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
BASE_REF = '1160c18f03fd318f0dec25738790935fa61379d4'
HEAD_REF = 'aa37da7fa8d5dc53823ccf99db8747e55cabb04b'

def git(*args):
    return subprocess.run(['git', *args], cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, check=True).stdout

population = {
    'TCSlib/Complexity/TuringMachine/Encoding.lean': ['changed owner; pairDiagTM and CodeTM/prerequisite context'],
    'TCSlib/Complexity/TuringMachine/Finite.lean': ['changed first-entry owner; bundled model/projections; published first halt'],
    'TCSlib/Complexity/TuringMachine/Build/Wrappers.lean': ['changed redirect owner; capture and canonical redirect controls'],
    'TCSlib/Complexity/TuringMachine/Build/Primitives.lean': ['changed incrementer owner; old emitter predicate/singleton first-entry comparison'],
    'TCSlib/Complexity/TuringMachine/Build/Catalog.lean': ['changed removal home; exact old-vs-current-MIG redirect proof comparison'],
    'TCSlib/Complexity/TuringMachine/Simulation.lean': ['unchanged230 prerequisite; left/right/action/buffer/branch/comp control definitions'],
    'TCSlib/Complexity/TuringMachine/Composition.lean': ['unchanged230 prerequisite; canonical zero-space operational context'],
    'TCSlib/Complexity/TuringMachine/Configuration.lean': ['actual configuration/action models, projections, initialization/movement controls'],
    'TCSlib/Complexity/TuringMachine/Deterministic.lean': ['actual run/step/space/visited models and published equations'],
    'TCSlib/Complexity/TuringMachine/StateRenaming.lean': ['conservative model-reader context; not claimed as a direct new-proof definition dependency'],
    'TCSlib/Complexity/TuringMachine/Build/Convention.lean': ['actual Cfg.ofWords full-definition control home'],
    'TCSlib/Complexity/TuringMachine/Build/Loop.lean': ['explicit old first-entry harvest comparison and source call sites'],
    'TCSlib/Complexity/TuringMachine/CodeSimulator.lean': ['explicit old first-entry harvest comparison requested by parent'],
    'TCSlib/Complexity/CookLevin/Hardness.lean': ['substantively inspected private clFirst reuse-search variant'],
    'TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean': ['substantively inspected private xr_firstArrival variants and public false positive'],
    'TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean': ['substantively inspected qy_emit_stop reuse-search false positive'],
}
population = dict(sorted(population.items()))
base = git('rev-parse', BASE_REF + '^{commit}').decode().strip()
head = git('rev-parse', HEAD_REF + '^{commit}').decode().strip()
for oid in [base, head]: git('cat-file', '-e', oid + '^{commit}')
branch = git('rev-parse', 'refs/heads/lean/mig1-followup-api').decode().strip()
origin = git('rev-parse', 'refs/remotes/origin/lean/mig1-followup-api').decode().strip()
assert branch == origin == head
changed = git('diff', '--name-only', base, head, '--', '*.lean').decode().splitlines()
expected = sorted(k for k, v in population.items() if any(t.startswith('changed') for t in v))
assert sorted(changed) == expected
scratch = Path(tempfile.mkdtemp(prefix='tcslib119-screen16-', dir='/private/tmp'))
receipt = dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(), base=base, head=head,
               branch=branch, local_origin_tracking=origin, network_checked=False,
               population=population, changed_files=changed, temporary_trees={}, sides={})
for label, oid in [('base', base), ('head', head)]:
    archive = git('archive', '--format=tar', oid, '--', *population)
    (OUT / (label + '.tar.base64.txt')).write_bytes(base64.encodebytes(archive))
    tree = scratch / label; tree.mkdir()
    rows = []
    with tarfile.open(fileobj=io.BytesIO(archive), mode='r:') as tf:
        regular = [m for m in tf.getmembers() if m.isfile()]
        assert sorted(m.name for m in regular) == sorted(population)
        for member in regular:
            path = member.name; data = tf.extractfile(member).read()
            blob = git('rev-parse', oid + ':' + path).decode().strip()
            git('cat-file', '-e', blob + '^{blob}')
            assert git('cat-file', 'blob', blob) == data
            assert hashlib.sha1(b'blob ' + str(len(data)).encode() + b'\0' + data).hexdigest() == blob
            target = tree / path; target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(data)
            inert = OUT / 'inputs' / label / (path + '.txt')
            inert.parent.mkdir(parents=True, exist_ok=True); inert.write_bytes(data)
            rows.append(dict(path=path, blob=blob, bytes=len(data), lines=len(data.splitlines()),
                             sha256=hashlib.sha256(data).hexdigest()))
    receipt['temporary_trees'][label] = str(tree)
    receipt['sides'][label] = dict(archive_bytes=len(archive), archive_sha256=hashlib.sha256(archive).hexdigest(), files=rows)
scripts = ['scripts/copy-text-screen-v3.py', 'scripts/campaign_style_lint.py', 'scripts/style_lint.py']
receipt['tools'] = {n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in scripts}
(OUT / 'capture.json').write_text(json.dumps(receipt, indent=2) + '\n')
(OUT / 'population.txt').write_text('\n'.join(population) + '\n')
(OUT / 'changed-files.txt').write_text('\n'.join(changed) + '\n')
print(json.dumps(dict(base=base, head=head, population_files=len(population), changed_files=len(changed),
    total_lines={s:sum(r['lines'] for r in receipt['sides'][s]['files']) for s in ['base','head']},
    temporary_trees=receipt['temporary_trees']), indent=2))
