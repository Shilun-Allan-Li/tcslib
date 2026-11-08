from pathlib import Path
import base64, datetime, hashlib, io, json, subprocess, tarfile, tempfile

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
BASE_REF = '3023dc1408c3d216fc07a7cbba9ae30135b861ed'
HEAD_REF = 'd0c4a292e781b55617e05b33fdd423bb059fd735'

def git(*args):
    return subprocess.run(['git', *args], cwd=ROOT, stdout=subprocess.PIPE,
                          stderr=subprocess.PIPE, check=True).stdout

population = {'TCSlib/Complexity/ClassNP/SAT.lean': ['actual SG1 owner repair and retained adapter/dispatcher/liveness families'], 'TCSlib/Complexity/ClassNP/Tautology.lean': ['standing round2 population; full original owner/consumer or disclosed debt comparison'], 'TCSlib/Complexity/CookLevin/Hardness.lean': ['actual SG1 owner repair; approved PolyTimePrefix import; retained adapter/dispatcher/liveness families'], 'TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean': ['standing round2 population; full original owner/consumer or disclosed debt comparison'], 'TCSlib/Complexity/TuringMachine/Build/Catalog.lean': ['standing round2 population; full original owner/consumer or disclosed debt comparison'], 'TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean': ['standing round2 population; full original owner/consumer or disclosed debt comparison'], 'TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean': ['standing round2 population; full original owner/consumer or disclosed debt comparison'], 'TCSlib/Complexity/TuringMachine/Build/Primitives.lean': ['standing round2 population; full original owner/consumer or disclosed debt comparison'], 'TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean': ['standing round2 population; full original owner/consumer or disclosed debt comparison'], 'TCSlib/Complexity/ClassNP/PolyTime.lean': ['published polynomial-time contracts and cited complexity definitions'], 'TCSlib/Complexity/ClassNP/PolyTimePairing.lean': ['published pairing polynomial-time contracts cited by actual repairs'], 'TCSlib/Complexity/ClassNP/PolyTimePrefix.lean': ['newly approved Hardness import and published prefix contract'], 'TCSlib/Complexity/TuringMachine/Encoding.lean': ['actual encoding/canonical-machine reader home'], 'TCSlib/Complexity/TuringMachine/Finite.lean': ['actual finite-machine bundle and model home'], 'TCSlib/Complexity/TuringMachine/Configuration.lean': ['actual configuration/tape/action model home'], 'TCSlib/Complexity/TuringMachine/Deterministic.lean': ['actual run/step/visited/space model and published reader home'], 'TCSlib/Complexity/ClassNP/CounterProgPolyTime.lean': ['named PolyTimePrefix import closure source'], 'TCSlib/Complexity/TuringMachine/CounterProg.lean': ['named PolyTimePrefix import closure source'], 'TCSlib/Complexity/TuringMachine/CounterProgInput.lean': ['named PolyTimePrefix import closure source'], 'TCSlib/Complexity/TuringMachine/CounterProgRun.lean': ['named PolyTimePrefix import closure source'], 'TCSlib/Complexity/TuringMachine/UnaryTape.lean': ['named PolyTimePrefix import closure source']}
population = dict(sorted(population.items()))
base = git('rev-parse', BASE_REF + '^{commit}').decode().strip()
head = git('rev-parse', HEAD_REF + '^{commit}').decode().strip()
for oid in [base, head]: git('cat-file', '-e', oid + '^{commit}')
branch = git('for-each-ref', '--format=%(refname)', '--points-at='+head, 'refs/heads').decode().splitlines()
origin = git('rev-parse', 'refs/remotes/origin/lean/dedup-sg1').decode().strip()
assert origin == head
changed = git('diff', '--name-only', base, head, '--', '*.lean').decode().splitlines()
expected = sorted(['TCSlib/Complexity/ClassNP/SAT.lean', 'TCSlib/Complexity/ClassNP/Tautology.lean', 'TCSlib/Complexity/CookLevin/Hardness.lean', 'TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean', 'TCSlib/Complexity/TuringMachine/Robustness/SingleTape.lean'])
assert sorted(changed) == expected
scratch = Path(tempfile.mkdtemp(prefix='tcslib106-r3-screen21-', dir='/private/tmp'))
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
scripts = ['scripts/copy-text-screen-v3.py']
receipt['tools'] = {n:hashlib.sha256((ROOT/n).read_bytes()).hexdigest() for n in scripts}
(OUT / 'capture.json').write_text(json.dumps(receipt, indent=2) + '\n')
(OUT / 'population.txt').write_text('\n'.join(population) + '\n')
(OUT / 'changed-files.txt').write_text('\n'.join(changed) + '\n')
print(json.dumps(dict(base=base, head=head, population_files=len(population), changed_files=len(changed),
    total_lines={s:sum(r['lines'] for r in receipt['sides'][s]['files']) for s in ['base','head']},
    temporary_trees=receipt['temporary_trees']), indent=2))
