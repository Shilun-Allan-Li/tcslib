#!/usr/bin/env python3
"""UNRUN candidate: exact committed checkpoint inventory, read-only Git/source reads.

Unlike freeze_global.py's explicitly labeled precommit mode, final audits require
one committed HEAD and exact source bytes. New owner names are NEVER enumerated by
hand. Rule10 closures remain the complete collector-derived conservative closures.
"""
import argparse
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys
sys.dont_write_bytecode = True

BASE = '5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
AREA = 'TCSlib/Cryptography/Obfuscation/'
FACADE = 'TCSlib/Cryptography/Obfuscation.lean'
EXPORT = 'TCSlib.lean'
VARIANTS = frozenset({'strict-A', 'strict-B', 'coe-A', 'coe-B'})


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def owner_path(path):
    return path.endswith('.lean') and (path == FACADE or path.startswith(AREA))


def resolve(root, ref):
    need(bool(re.fullmatch(r'[A-Za-z0-9_./-]+', ref)) and not ref.startswith('-'), 'Unsafe ref')
    return git(root, 'rev-parse', '--verify', ref + '^{commit}').decode().strip()


def read_diff(root, base, head):
    fields = git(root, 'diff', '--no-renames', '--name-status', '-z', base, head, '--').split(b'\0')
    need(fields[-1] == b'', 'Incomplete NUL diff')
    fields.pop()
    need(len(fields) % 2 == 0, 'Unexpected diff layout/rename')
    rows = {}
    for index in range(0, len(fields), 2):
        status, path = fields[index].decode(), fields[index + 1].decode()
        need(status in {'A', 'M'}, 'Deletion/type change/rename needs explicit review: ' + path)
        need(path not in rows, 'Duplicate changed path')
        need(owner_path(path) or path == EXPORT, 'Out-of-scope committed path: ' + path)
        rows[path] = status
    need(rows, 'Empty checkpoint diff')
    return rows


def builder(root):
    path = root / 'evidence/tools/seal/review/archived-gate10-tools/build_seals.py'
    spec = importlib.util.spec_from_file_location('checkpoint_reviewed_header', path)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def canonical(payload):
    return json.dumps(payload, sort_keys=True, separators=(',', ':'), ensure_ascii=False).encode()


def build(root, head='HEAD', historical=False):
    root = Path(root).resolve()
    head = resolve(root, head)
    subprocess.run(['git', '-C', str(root), 'merge-base', '--is-ancestor', BASE, head], check=True)
    if not historical:
        need(head == resolve(root, 'HEAD'), 'Final inventory must identify current committed HEAD')
        untracked = git(root, 'ls-files', '--others', '-z', '--', FACADE, AREA).split(b'\0')
        need(not [x.decode() for x in untracked if x and owner_path(x.decode())],
             'Uncommitted/untracked owner source; use precommit freeze guard first')
    changes = read_diff(root, BASE, head)
    bs = builder(root)
    blobs = {path: git(root, 'show', head + ':' + path) for path in changes}
    if not historical:
        for path, raw in blobs.items():
            need((root / path).is_file() and not (root / path).is_symlink()
                 and (root / path).read_bytes() == raw, 'Source differs from committed HEAD: ' + path)
    # The sole allowed root edit remains exactly the export import, never a new declaration.
    if EXPORT in blobs:
        old = git(root, 'show', BASE + ':' + EXPORT).decode()
        before = [x.strip() for x in bs.blank_comments_strings(old).splitlines() if x.strip()]
        after = [x.strip() for x in bs.blank_comments_strings(blobs[EXPORT].decode()).splitlines()
                 if x.strip()]
        from collections import Counter
        need(not Counter(before) - Counter(after), 'Root export removes/changes a command')
        need(Counter(after) - Counter(before) == Counter({'import TCSlib.Cryptography.Obfuscation': 1}),
             'Root export is not the exact approved single import')
        added_import = 'import TCSlib.Cryptography.Obfuscation'
        need(any(command == added_import and after[:index] + after[index + 1:] == before
                 for index, command in enumerate(after)),
             'Root export reorders existing commands instead of only inserting the approved import')
    owners = {path[:-5].replace('/', '.'): path for path in changes if owner_path(path)}
    need(owners and len(owners) == sum(owner_path(path) for path in changes), 'Owner collision/empty')
    imports, closure_sources, mathlib = {}, {}, set()
    todo = list(owners)
    while todo:
        module = todo.pop()
        if module in imports:
            continue
        path = module.replace('.', '/') + '.lean'
        raw = blobs.get(path)
        if raw is None:
            raw = git(root, 'show', head + ':' + path)
        if not historical:
            need((root / path).read_bytes() == raw, 'Imported TCSlib source is not HEAD: ' + path)
        deps = bs.header(raw)['imports']
        imports[module] = deps
        closure_sources[path] = sha(raw)
        for dep in deps:
            if dep == 'TCSlib' or dep.startswith('TCSlib.'):
                todo.append(dep)
            elif dep == 'Mathlib' or dep.startswith('Mathlib.'):
                mathlib.add(dep)
    ordered, seen, visiting = [], set(), set()

    def visit(module):
        if module in seen:
            return
        need(module not in visiting, 'Owned import cycle: ' + module)
        visiting.add(module)
        for dep in imports[module]:
            if dep in owners:
                visit(dep)
        visiting.remove(module)
        seen.add(module)
        ordered.append(module)

    for module in sorted(owners):
        visit(module)
    inventory = {
        'schema': 2, 'root': str(root), 'base': BASE, 'head': head,
        'tree': git(root, 'rev-parse', head + '^{tree}').decode().strip(),
        'mode': 'HISTORICAL_COMMIT' if historical else 'COMMITTED_HEAD',
        'owners': ordered,
        'owner_sources': {module: {'file': owners[module], 'sha256': sha(blobs[owners[module]]),
                                   'status': changes[owners[module]]} for module in ordered},
        'changed_paths': changes,
        'source_sha256': {path: sha(raw) for path, raw in blobs.items()},
        'tcslib_import_closure': sorted(imports), 'imports': imports,
        'closure_source_sha256': closure_sources, 'mathlib_direct_roots': sorted(mathlib),
        'qualification': 'Direct Mathlib roots are every Mathlib import in the full TCSlib source '
                         'closure, not Mathlib transitive closure or only newly missing oleans. '
                         'No cache command is run by this inventory.'}
    inventory['inventory_sha256'] = sha(canonical(inventory))
    return inventory


def load(path, root=None, require_current=True):
    data = json.loads(Path(path).read_text())
    actual_root = Path(root or data['root']).resolve()
    need(data['base'] == BASE and data['root'] == str(actual_root), 'Inventory base/worktree differs')
    payload = dict(data)
    digest = payload.pop('inventory_sha256')
    need(sha(canonical(payload)) == digest, 'Inventory digest differs')
    if require_current:
        need(data['mode'] == 'COMMITTED_HEAD', 'Final audit cannot use a worktree/historical inventory')
    recomputed = build(actual_root, data['head'], historical=data['mode'] == 'HISTORICAL_COMMIT')
    need(recomputed == data, 'Inventory does not equal independently rederived complete current snapshot')
    return data


def files(data):
    return [data['owner_sources'][module]['file'] for module in data['owners']]


def exact_keys(actual, expected, label):
    values = list(actual)
    need(len(values) == len(set(values)) and set(values) == set(expected), label + ' key set differs')


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', default='.')
    ap.add_argument('--head', default='HEAD')
    ap.add_argument('--historical', action='store_true')
    ap.add_argument('--roots-baseline', help='Prior exact DIRECT Mathlib root list; no cache is run')
    ap.add_argument('--out', required=True, help='Fresh snapshot directory')
    args = ap.parse_args()
    out = Path(args.out)
    need(not out.exists(), 'Choose a fresh snapshot directory')
    inventory = build(args.root, args.head, args.historical)
    out.mkdir(parents=True)
    (out / 'inventory.json').write_text(json.dumps(inventory, indent=2) + '\n')
    (out / 'owners.txt').write_text('\n'.join(inventory['owners']) + '\n')
    (out / 'files.txt').write_text('\n'.join(files(inventory)) + '\n')
    (out / 'owner-paths.txt').write_text('\n'.join(path[:-5] for path in files(inventory)) + '\n')
    (out / 'mathlib-direct-roots.txt').write_text('\n'.join(inventory['mathlib_direct_roots']) + '\n')
    if args.roots_baseline:
        prior = set(Path(args.roots_baseline).read_text().split())
        now = set(inventory['mathlib_direct_roots'])
        delta = {'added_direct_roots': sorted(now - prior), 'removed_direct_roots': sorted(prior - now),
                 'baseline_sha256': sha(Path(args.roots_baseline).read_bytes()),
                 'cache_refresh_verified': False,
                 'qualification': 'Any required narrowed cache refresh is root-only under the pinned '
                                  'slot wrapper. Existing transitive availability does not erase a new direct root.'}
        (out / 'root-delta.json').write_text(json.dumps(delta, indent=2) + '\n')
    print('CHECKPOINT_INVENTORY', inventory['head'], len(inventory['owners']), 'owners',
          len(inventory['mathlib_direct_roots']), 'direct Mathlib roots')


if __name__ == '__main__':
    main()
