"""Prepare/check all checkpoint-2 changed files, preserving every Rule-10 result.

Use python3 -I. --run requires the coordinator's released OUR compiler slot.
No owned Lean source is edited. --labels selects an explicit checkpoint subset;
omitted final-file checks remain pending. Each selected file gets a snapshot/census and A/B
probes with six paired controls; source failures never suppress the other mode
or later files. Guard interruptions are reported separately and retried with a
fresh raw-attempt directory. Definitions absent from the issue base are recorded
as absent, rather than given fabricated baseline seals.
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
PREFIX = 'TCSlib.Cryptography.Authentication.Signatures.Lamport'
TARGETS = [
    ('Main', PREFIX), ('Encoding', PREFIX + '.Encoding'), ('Planted', PREFIX + '.Planted'),
    ('TableCoins', PREFIX + '.TableCoins'), ('Averaging', PREFIX + '.Averaging'),
    ('AveragingExtra', PREFIX + '.AveragingExtra'), ('Statistics', PREFIX + '.Statistics'),
    ('Experiment', PREFIX + '.Experiment'),
    ('Auth', 'TCSlib.Cryptography.Authentication')]


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def utc():
    return datetime.datetime.now(datetime.timezone.utc).isoformat()


def dump(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def git_source(root, revision, module):
    return subprocess.run(['git', '-C', str(root), 'show',
                           revision + ':' + module.replace('.', '/') + '.lean'],
                          capture_output=True)


def verify_sources(root, commit):
    head = subprocess.check_output(['git', '-C', str(root), 'rev-parse', 'HEAD'], text=True).strip()
    if head != commit:
        raise RuntimeError('HEAD differs from checkpoint source commit')
    rows = []
    for label, module in TARGETS:
        pinned = git_source(root, commit, module)
        current = (root / (module.replace('.', '/') + '.lean')).read_bytes()
        if pinned.returncode or pinned.stdout != current:
            raise RuntimeError('checkpoint source differs from working bytes: ' + module)
        rows.append(dict(label=label, module=module, source_sha256=sha(current)))
    return rows


def harden_inventory(root, evidence, phase):
    # Same strict canonical-home assertion used by the BaseAuth transaction.
    directory = evidence / 'seals' / phase
    manifest_path = directory / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    path = root / (manifest['inventory_module'].replace('.', '/') + '.lean')
    raw = path.read_bytes()
    (directory / 'Inventory.pre-exact-closure.lean').write_bytes(raw)
    anchor = '  let mut rows : Array String := #[]\n'
    addition = '''  let unexpected := env.header.moduleNames.toList.filter fun m =>
    (`TCSlib).isPrefixOf m && !(homes.contains m.toString)
  unless unexpected.isEmpty do
    throwError "LAMP-INVENTORY unexpected TCSlib homes {unexpected}"
  logInfo m!"LAMP-CLOSURE-EXACT\\t{target}\\t{homes.length}"
'''
    if raw.decode().count(anchor) != 1:
        raise RuntimeError('inventory insertion is not unique')
    result = raw.decode().replace(anchor, addition + anchor).encode()
    path.write_bytes(result)
    (directory / 'Inventory.lean').write_bytes(result)
    manifest.update(inventory_pre_exact_closure_sha256=sha(raw),
                    inventory_sha256=sha(result),
                    inventory_transform='reject unexpected canonical TCSlib import homes')
    dump(manifest_path, manifest)
    return manifest


def run(args, rows):
    root, evidence = Path(args.root).resolve(), Path(args.evidence).resolve()
    tools = evidence / 'tools'
    directory = evidence / 'logs' / 'checkpoint2-seals' / args.attempt
    directory.mkdir(parents=True, exist_ok=False)
    (directory / Path(__file__).name).write_bytes(Path(__file__).read_bytes())
    selected = [(label, module) for label, module in TARGETS
                if args.labels is None or label in args.labels]
    dump(directory / 'metadata.json', dict(start=utc(), commit=args.commit,
         root=str(root), source_audit_targets=rows, executed_targets=selected,
         script_sha256=sha(Path(__file__).read_bytes()),
         phase_prefix=args.phase_prefix, no_owned_source_edits=True, serial=True))
    absent = []
    for label, module in TARGETS:
        if not module.startswith(PREFIX + '.'):
            continue
        probe = git_source(root, BASE, module)
        if probe.returncode == 0:
            raise RuntimeError('helper exists at base and requires real baseline evidence: ' + module)
        absent.append(dict(module=module, revision=BASE, source_absent=True,
                           git_status=probe.returncode, git_stderr=probe.stderr.decode()))
    dump(directory / 'base-absent-helpers.json', absent)
    env = os.environ.copy()
    scratch = directory / 'scratch'
    scratch.mkdir()
    env['TMPDIR'] = str(scratch)
    results, commands, fatal = [], [], None
    transcript = directory / 'orchestrator.log'
    with transcript.open('w') as output:
        def command(argv, label, require=True):
            output.write('UTC ' + utc() + '\nCOMMAND ' + json.dumps(argv) + '\n')
            output.flush()
            status = subprocess.run(argv, cwd=root, env=env, stdout=output,
                                    stderr=subprocess.STDOUT).returncode
            commands.append(dict(label=label, status=status, command=argv, end=utc()))
            output.flush()
            if status and require:
                raise RuntimeError(label + ' exited ' + str(status))
            return status

        def check(module, tag):
            retry = 0
            while True:
                retry += 1
                actual_tag = tag if retry == 1 else tag + '-host' + str(retry)
                attempt = args.attempt + '-' + actual_tag
                status = command(['python3', '-I', str(tools / 'check_helper.py'),
                                  module.replace('.', '/'), attempt], actual_tag, require=False)
                if status == 130:
                    output.write('RETRY HOST-INTERRUPTED INVENTORY MODULE ' + actual_tag + '\n')
                    output.flush()
                    continue
                if status:
                    raise RuntimeError(actual_tag + ' exited ' + str(status))
                return attempt

        try:
            for label, target in selected:
                verify_sources(root, args.commit)
                phase = args.phase_prefix + label
                command(['python3', '-I', str(tools / 'prepare_seals.py'), 'inventory',
                         '--root', str(root), '--evidence', str(evidence), '--phase', phase,
                         '--revision', args.commit, target], label + '-prepareInventory')
                preparation = harden_inventory(root, evidence, phase)
                inventory_order = evidence / 'seals' / phase / 'inventory-order.txt'
                successful_inventory_attempt = None
                for index, module in enumerate(inventory_order.read_text().splitlines()):
                    successful_inventory_attempt = check(
                        module.replace('/', '.'), label + '-inventory' + str(index))
                inventory_log = evidence / 'logs' / 'helper-checks' / (
                    'Inventory-' + successful_inventory_attempt + '.log')
                command(['python3', '-I', str(tools / 'prepare_seals.py'), 'prepare',
                         '--root', str(root), '--evidence', str(evidence), '--phase', phase,
                         '--catalog-log', str(inventory_log)], label + '-prepareSeals')
                command(['python3', '-I', str(tools / 'prepare_seals.py'), 'scan',
                         '--root', str(root), '--evidence', str(evidence), '--phase', phase,
                         '--catalog-log', str(inventory_log), target], label + '-scan')
                retry = 0
                while True:
                    retry += 1
                    attempt = args.attempt + '-' + label + '-r' + str(retry)
                    manifest = evidence / 'seals' / phase / 'seal-manifest.json'
                    status = command(['python3', '-I', str(tools / 'run_seals.py'),
                                      '--root', str(root), '--evidence', str(evidence),
                                      '--manifest', str(manifest), '--attempt', attempt],
                                     label + '-seals-r' + str(retry), require=False)
                    raw = evidence / 'logs' / 'seals' / attempt
                    summary = json.loads((raw / 'summary.json').read_text())
                    actual = [json.loads(line) for line in (raw / 'results.jsonl').read_text().splitlines()]
                    host_interrupted = any(record['exit'] == 130 for record in actual)
                    results.append(dict(target=target, label=label, phase=phase,
                                        attempt=attempt, status=status, summary=summary,
                                        host_interrupted=host_interrupted))
                    dump(directory / 'progress.json', results)
                    if summary.get('resource_stop'):
                        raise RuntimeError('E-RES in ' + attempt)
                    if host_interrupted:
                        output.write('RETRY HOST-INTERRUPTED SEAL QUEUE ' + attempt + '\n')
                        output.flush()
                        continue
                    # Preserve source B failures and continue every other file/control.
                    if not summary['queue_complete']:
                        raise RuntimeError('incomplete non-resource seal queue: ' + attempt)
                    if not summary['all_harnesses_and_controls_valid']:
                        raise RuntimeError('invalid seal harness/control: ' + attempt)
                    if any(item.get('mode') == 'A' and item['status'] == 'SOURCE_FAIL'
                           for item in actual):
                        raise RuntimeError('actual seal A failure needs native fix: ' + attempt)
                    break
            verify_sources(root, args.commit)
        except BaseException as exc:
            fatal = repr(exc)
            output.write('QUEUE STOPPED ' + fatal + '\n')
        latest = {}
        for record in results:
            if not record['host_interrupted']:
                latest[record['target']] = record
        a_failures, b_failures, invalid = [], [], []
        for target, record in latest.items():
            raw = evidence / 'logs' / 'seals' / record['attempt'] / 'results.jsonl'
            for line in raw.read_text().splitlines():
                item = json.loads(line)
                if item['status'] not in ('SOURCE_PASS', 'SOURCE_FAIL', 'CONTROL_PASS'):
                    invalid.append(dict(target=target, attempt=record['attempt'], probe=item))
                if item.get('mode') in ('A', 'B') and item['status'] == 'SOURCE_FAIL':
                    dest = a_failures if item['mode'] == 'A' else b_failures
                    dest.append(dict(target=target, attempt=record['attempt'], probe=item))
        summary = dict(end=utc(), fatal=fatal, targets_requested=len(selected),
                       targets_finished=len(latest), all_controls_and_harnesses_valid=not invalid,
                       all_A_pass=not a_failures, A_failures=a_failures, B_failures=b_failures,
                       invalid_results=invalid, attempts=results, commands=commands,
                       source_commit=args.commit,
                       interpretation='B failures are retained in full, never treated as A passes. '
                                      'Compare them with the separately delivered pinned base B results.')
        dump(directory / 'summary.json', summary)
    print(json.dumps({k:summary[k] for k in ['fatal','targets_requested','targets_finished',
                                           'all_controls_and_harnesses_valid','all_A_pass']}, indent=2))
    print('Full result and raw failure lists:', directory / 'summary.json')
    return 0 if fatal is None and len(latest) == len(selected) and not invalid and not a_failures else 1


parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', required=True)
parser.add_argument('--evidence', required=True)
parser.add_argument('--commit', required=True)
parser.add_argument('--phase-prefix', required=True)
parser.add_argument('--attempt', required=True)
parser.add_argument('--labels', nargs='+', choices=[label for label, _ in TARGETS])
parser.add_argument('--run', action='store_true')
args = parser.parse_args()
if not re.fullmatch(r'[A-Za-z][A-Za-z0-9]*', args.phase_prefix):
    raise RuntimeError('phase prefix must be a Lean identifier')
if not re.fullmatch(r'[A-Za-z0-9][A-Za-z0-9_-]*', args.attempt):
    raise RuntimeError('attempt must be a fresh simple name')
rows = verify_sources(Path(args.root).resolve(), args.commit)
if args.run:
    sys.exit(run(args, rows))
print(json.dumps(dict(commit=args.commit, targets=rows), indent=2))
