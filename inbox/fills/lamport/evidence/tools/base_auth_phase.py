"""Check the pinned base Authentication facade with exact canonical base dependencies.

Use python3 -I. Without --run this only prints a source/olean audit and planned
queue; it neither edits proof sources nor invokes Lean. --run is for the
coordinator's explicitly released compiler slot. It temporarily checks canonical
base Lamport and HashAndSign in OUR existing olean tree, runs the base facade
snapshot/inventory/seals, then restores the exact saved final Lamport bytes and
rechecks final Lamport, HashAndSign and Authentication. It never copies, joins,
renames, removes or restores an olean/dependency tree.
"""
import argparse
import datetime
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys

BASE = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
AUTH = 'TCSlib.Cryptography.Authentication'
LAMPORT = 'TCSlib.Cryptography.Authentication.Signatures.Lamport'
HASH_SIGN = 'TCSlib.Cryptography.Authentication.Signatures.HashAndSign'


def digest(raw):
    return hashlib.sha256(raw).hexdigest()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def source_path(root, module):
    return root / (module.replace('.', '/') + '.lean')


def git_source(root, module, revision=BASE):
    return subprocess.check_output(['git', '-C', str(root), 'show',
                                   revision + ':' + module.replace('.', '/') + '.lean'])


def imports(raw):
    # All pinned closure imports occupy ordinary top-level import lines.
    return [word for line in raw.decode().splitlines() if line.startswith('import ')
            for word in line.split()[1:] if word.startswith('TCSlib.')]


def pinned_graph(root):
    graph, sources = {}, {}

    def visit(module):
        if module in graph:
            return
        raw = git_source(root, module)
        sources[module] = raw
        graph[module] = imports(raw)
        for child in graph[module]:
            visit(child)

    visit(AUTH)
    return graph, sources


def plan(root, final_commit=None):
    graph, sources = pinned_graph(root)
    ol = (root / '.lake/tcslib-check-oleans').resolve()
    configured_ol = Path(os.environ.get('TCSLIB_OLEANS', str(ol))).resolve()
    if configured_ol != ol:
        raise RuntimeError('require OUR usual single olean tree, got ' + str(configured_ol))
    memo = {}

    def affected(module):
        if module not in memo:
            memo[module] = module == LAMPORT or any(affected(dep) for dep in graph[module])
        return memo[module]

    descendants = sorted(module for module in graph if affected(module))
    if descendants != sorted([AUTH, LAMPORT, HASH_SIGN]):
        raise RuntimeError('base closure has additional Lamport consumers: ' + repr(descendants))
    rows = []
    for module in sorted(graph):
        current = source_path(root, module).read_bytes()
        differs = current != sources[module]
        if differs and module not in (AUTH, LAMPORT):
            raise RuntimeError('foreign pinned-base source differs: ' + module)
        olean = ol / (module.replace('.', '/') + '.olean')
        # The facade's own canonical olean is not imported by its snapshot.
        if module not in (AUTH, LAMPORT, HASH_SIGN) and (
                not olean.is_file() or olean.stat().st_size == 0):
            raise RuntimeError('missing canonical prerequisite olean: ' + str(olean))
        rows.append(dict(module=module, source_base_sha256=digest(sources[module]),
                         source_working_sha256=digest(current), differs_from_base=differs,
                         olean=str(olean),
                         olean_sha256=digest(olean.read_bytes()) if olean.is_file() else None))
    head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    if final_commit and head != final_commit:
        raise RuntimeError('HEAD differs from frozen source commit')
    data = dict(utc=utc(), base=BASE, head=head, final_commit=final_commit,
                root=str(root), sole_tcs_olean_tree=str(ol), closure_count=len(graph),
                lamport_consumers=descendants,
                different_source_modules=[r['module'] for r in rows if r['differs_from_base']],
                canonical_base_checks=[LAMPORT, HASH_SIGN],
                base_phase='pinned Authentication snapshot, inventory, A/B and six controls',
                canonical_final_checks=[LAMPORT, HASH_SIGN, AUTH],
                provider_rows=rows,
                rationale='Only Lamport, HashAndSign and Authentication transitively depend on '
                          'Lamport in the pinned facade closure. All other provider sources '
                          'are byte-identical to the pinned base and their existing oleans '
                          'come from the already recorded bootstrap/checks of this worker.')
    return data, sources


def write_json(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def strict_inventory(root, evidence, phase):
    """Strengthen only this new inventory, retaining its pre-transform provenance."""
    directory = evidence / 'seals' / phase
    manifest_path = directory / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    module = manifest['inventory_module']
    path = source_path(root, module)
    raw = path.read_bytes()
    (directory / 'Inventory.pre-exact-closure.lean').write_bytes(raw)
    anchor = '  let mut rows : Array String := #[]\n'
    addition = '''  let unexpected := env.header.moduleNames.toList.filter fun m =>
    (`TCSlib).isPrefixOf m && !(homes.contains m.toString)
  unless unexpected.isEmpty do
    throwError "LAMP-INVENTORY unexpected TCSlib homes {unexpected}"
  logInfo m!"LAMP-CLOSURE-EXACT\\t{target}\\t{homes.length}"
'''
    text = raw.decode()
    if text.count(anchor) != 1:
        raise RuntimeError('inventory insertion anchor is not unique')
    result = text.replace(anchor, addition + anchor).encode()
    path.write_bytes(result)
    (directory / 'Inventory.lean').write_bytes(result)
    manifest['inventory_pre_exact_closure_sha256'] = digest(raw)
    manifest['inventory_sha256'] = digest(result)
    manifest['inventory_transform'] = 'reject any unexpected canonical TCSlib import home'
    write_json(manifest_path, manifest)
    return module


def run(args, audit, sources):
    root, evidence = Path(args.root).resolve(), Path(args.evidence).resolve()
    directory = evidence / 'logs' / 'base-auth' / args.attempt
    directory.mkdir(parents=True, exist_ok=False)
    transcript = directory / 'orchestrator.log'
    lamport_path = source_path(root, LAMPORT)
    final_lamport = lamport_path.read_bytes()
    final_auth = source_path(root, AUTH).read_bytes()
    (directory / 'Lamport.final-working.lean').write_bytes(final_lamport)
    (directory / 'Authentication.final-working.lean').write_bytes(final_auth)
    (directory / 'Lamport.pinned-base.lean').write_bytes(sources[LAMPORT])
    (directory / 'Authentication.pinned-base.lean').write_bytes(sources[AUTH])
    audit.update(phase=args.phase, attempt=args.attempt,
                 final_lamport_sha256=digest(final_lamport),
                 final_auth_sha256=digest(final_auth),
                 tool_sha256=digest(Path(__file__).read_bytes()))
    write_json(directory / 'preconditions.json', audit)
    (directory / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    tools = evidence / 'tools'
    env = os.environ.copy()
    scratch = directory / 'scratch'
    scratch.mkdir()
    env['TMPDIR'] = str(scratch)
    checks, error, restored, final_ok = [], None, False, False

    def command(argv, label, stdout, require=True):
        stdout.write('UTC ' + utc() + '\nCOMMAND ' + json.dumps(argv) + '\n')
        stdout.flush()
        status = subprocess.run(argv, cwd=root, env=env, stdout=stdout,
                                stderr=subprocess.STDOUT).returncode
        checks.append(dict(label=label, command=argv, status=status, end=utc()))
        stdout.flush()
        if status and require:
            raise RuntimeError(f'{label} exited {status}')
        return status

    def module_check(module, label, stdout):
        retry = 0
        while True:
            retry += 1
            tag = label if retry == 1 else label + '-host' + str(retry)
            status = command(['python3', '-I', str(tools / 'check_helper.py'),
                              module.replace('.', '/'), args.attempt + '-' + tag],
                             tag, stdout, require=False)
            if status == 130:
                stdout.write('RETRY HOST-INTERRUPTED MODULE ' + tag + '\n')
                stdout.flush()
                continue
            if status:
                raise RuntimeError(f'{tag} exited {status}')
            return args.attempt + '-' + tag

    def stable_providers():
        for row in audit['provider_rows']:
            module = row['module']
            if module in (AUTH, LAMPORT, HASH_SIGN):
                continue
            if digest(source_path(root, module).read_bytes()) != row['source_base_sha256']:
                raise RuntimeError('provider source changed during base phase: ' + module)
            if digest(Path(row['olean']).read_bytes()) != row['olean_sha256']:
                raise RuntimeError('provider olean changed during base phase: ' + module)

    with transcript.open('w') as output:
        try:
            # No other task may edit/check this proof clone during this phase.
            stable_providers()
            lamport_path.write_bytes(sources[LAMPORT])
            module_check(LAMPORT, 'baseLamport', output)
            module_check(HASH_SIGN, 'baseHashSign', output)
            stable_providers()
            pinned_products = {}
            for module in (LAMPORT, HASH_SIGN):
                file = Path(audit['sole_tcs_olean_tree']) / (module.replace('.', '/') + '.olean')
                pinned_products[module] = digest(file.read_bytes())
            write_json(directory / 'fresh-base-canonical-products.json', pinned_products)
            if args.resume_manifest:
                # Only a host-interrupted probe is retried. All original phase sources,
                # catalog, requests and successful raw probes remain immutable.
                original = Path(args.resume_provenance).resolve()
                old_audit = json.loads((original / 'preconditions.json').read_text())
                old_products = json.loads((original / 'fresh-base-canonical-products.json').read_text())
                if old_audit['base'] != BASE or old_products != pinned_products:
                    raise RuntimeError('canonical base products differ from original census environment')
                old_rows = {r['module']:r for r in old_audit['provider_rows']}
                for row in audit['provider_rows']:
                    before = old_rows[row['module']]
                    if row['source_base_sha256'] != before['source_base_sha256']:
                        raise RuntimeError('pinned source provenance differs on resume')
                    if row['module'] not in (AUTH, LAMPORT, HASH_SIGN):
                        if row['olean_sha256'] != before['olean_sha256']:
                            raise RuntimeError('unchanged base provider differs on resume')
                seal_manifest = Path(args.resume_manifest).resolve()
                if seal_manifest.parent != evidence / 'seals' / args.phase:
                    raise RuntimeError('resume manifest must retain its original preparation directory')
                write_json(directory / 'same-base-environment-as-original.json',
                           dict(original=str(original), products=pinned_products,
                                all_147_unchanged_provider_olean_hashes_equal=True,
                                canonical_base_products_bit_identical=True,
                                resume_manifest_sha256=digest(seal_manifest.read_bytes())))
            else:
                command(['python3', '-I', str(tools / 'prepare_seals.py'), 'inventory',
                         '--root', str(root), '--evidence', str(evidence), '--phase', args.phase,
                         '--revision', BASE, AUTH], 'prepareInventory', output)
                inventory = strict_inventory(root, evidence, args.phase)
                order = evidence / 'seals' / args.phase / 'inventory-order.txt'
                successful_inventory_attempt = None
                for index, module in enumerate(order.read_text().splitlines()):
                    successful_inventory_attempt = module_check(
                        module.replace('/', '.'), f'inventory{index}', output)
                inventory_log = evidence / 'logs' / 'helper-checks' / (
                    'Inventory-' + successful_inventory_attempt + '.log')
                ends = [line.split('\t') for line in inventory_log.read_text().splitlines()
                        if line.startswith('LAMP-INVENTORY-END\t' + AUTH + '\t')]
                if len(ends) != 1 or ends[0][3:] != ['0', str(audit['closure_count'] - 1)]:
                    raise RuntimeError('base facade census did not certify zero own constants/full closure')
                command(['python3', '-I', str(tools / 'prepare_seals.py'), 'prepare',
                         '--root', str(root), '--evidence', str(evidence), '--phase', args.phase,
                         '--catalog-log', str(inventory_log)], 'prepareSeals', output)
                seal_manifest = evidence / 'seals' / args.phase / 'seal-manifest.json'
            retry = 0
            while True:
                retry += 1
                seal_attempt = args.attempt + '-seals' + ('' if retry == 1 else '-host' + str(retry))
                status = command(['python3', '-I', str(tools / 'run_seals.py'), '--root', str(root),
                                  '--evidence', str(evidence), '--manifest', str(seal_manifest),
                                  '--attempt', seal_attempt], 'runSeals' + str(retry), output,
                                 require=False)
                actual = [json.loads(line) for line in
                          (evidence / 'logs/seals' / seal_attempt / 'results.jsonl').read_text().splitlines()]
                if args.resume_manifest and any(row['exit'] == 130 for row in actual):
                    output.write('RETRY HOST-INTERRUPTED FILTERED SEALS ' + seal_attempt + '\n')
                    output.flush()
                    continue
                if status:
                    raise RuntimeError('runSeals exited ' + str(status))
                break
            stable_providers()
            for module, expected in pinned_products.items():
                file = Path(audit['sole_tcs_olean_tree']) / (module.replace('.', '/') + '.olean')
                if digest(file.read_bytes()) != expected:
                    raise RuntimeError('canonical base product changed during seal phase: ' + module)
            # Facades have no proof commands; scan the immutable pinned raw source.
            raw = sources[AUTH].decode()
            code = re.sub(r'/\-.*?\-/', '', raw, flags=re.S)
            operations = re.findall(r'\b(?:unfold|delta|simp|simpa|rw|rwa|erw|dsimp)\b', code)
            if operations:
                raise RuntimeError('facade gained proof commands; needs full explicit-unfold scan')
            write_json(directory / 'explicit-unfold-scan-base-auth.json',
                       dict(target=AUTH, revision=BASE, source_sha256=digest(sources[AUTH]),
                            source='Authentication.pinned-base.lean', operations=[],
                            local_declarations=0))
        except BaseException as exc:
            error = repr(exc)
            output.write('BASE PHASE ERROR ' + error + '\n')
        finally:
            # Exact-byte restoration happens even if a baseline probe/control fails.
            lamport_path.write_bytes(final_lamport)
            restored = digest(lamport_path.read_bytes()) == digest(final_lamport)
            output.write('RESTORED FINAL LAMPORT ' + str(restored) + '\n')
            if source_path(root, AUTH).read_bytes() != final_auth:
                error = (error or '') + '; final Authentication source changed unexpectedly'
            try:
                if not restored:
                    raise RuntimeError('final source restoration hash mismatch')
                for module, label in [(LAMPORT, 'finalLamport'),
                                      (HASH_SIGN, 'finalHashSign'), (AUTH, 'finalAuth')]:
                    module_check(module, label, output)
                final_ok = True
            except BaseException as exc:
                error = (error or '') + '; final rebuild stopped at prerequisite failure: ' + repr(exc)
            write_json(directory / 'summary.json', dict(end=utc(), base_phase_error=error,
                       source_restored=restored, final_rebuild_ok=final_ok, checks=checks))
    print(json.dumps(dict(source_restored=restored, final_rebuild_ok=final_ok,
                          error=error, transcript=str(transcript)), indent=2))
    return 0 if error is None and restored and final_ok else 1


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True)
parser.add_argument('--evidence', required=True)
parser.add_argument('--phase', required=True)
parser.add_argument('--attempt', required=True)
parser.add_argument('--final-commit')
parser.add_argument('--resume-manifest')
parser.add_argument('--resume-provenance')
parser.add_argument('--run', action='store_true')
args = parser.parse_args()
if bool(args.resume_manifest) != bool(args.resume_provenance):
    raise RuntimeError('resume requires both filtered manifest and original provenance directory')
if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*', args.phase):
    raise RuntimeError('phase must be a fresh Lean identifier')
if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]*', args.attempt):
    raise RuntimeError('attempt must be a fresh simple path component')
audit, sources = plan(Path(args.root).resolve(), args.final_commit)
issued_order = Path(args.evidence).resolve() / 'inputs/order.txt'
issued_modules = {line.strip().replace('/', '.') for line in issued_order.read_text().splitlines()
                  if line.strip()}
if issued_modules != {row['module'] for row in audit['provider_rows']}:
    raise RuntimeError('pinned Authentication closure differs from the issued bootstrap order')
audit['closure_equals_issued_150_order'] = True
if args.run:
    if not args.final_commit:
        raise RuntimeError('--run requires the coordinator-frozen --final-commit')
    sys.exit(run(args, audit, sources))
print(json.dumps(audit, indent=2))
