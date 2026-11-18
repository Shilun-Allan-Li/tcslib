#!/usr/bin/env python3
"""UNRUN candidate: global frozen public-header/prose guard; no Lean or Git mutation.

Precommit mode binds an exact WORKTREE_CANDIDATE source inventory, never claims HEAD
source equality. M0 owners come from the pinned Lean-base..M0 Git diff. Per-file
original decls2 output is retained and fully reconciled with explicit move ledgers.
"""
import argparse
import ast
from collections import Counter
import datetime
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

BASE = '5ed465f62e4ae0f93ded1a1ba49e807591b589eb'
FACADE = 'TCSlib/Cryptography/Obfuscation.lean'
PREFIX = 'TCSlib/Cryptography/Obfuscation/'


def need(ok, message):
    if not ok:
        raise RuntimeError(message)


def sha(raw):
    return hashlib.sha256(raw).hexdigest()


def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args])


def owned(path):
    return path.endswith('.lean') and (path == FACADE or path.startswith(PREFIX))


def parser_functions(path, names, assignments=()):
    """Reuse reviewed functions without executing the CLI/top-level Git loops."""
    raw = path.read_text()
    tree = ast.parse(raw, filename=str(path))
    nodes = []
    for node in tree.body:
        if isinstance(node, (ast.Import, ast.ImportFrom)):
            nodes.append(node)
        elif isinstance(node, ast.FunctionDef) and node.name in names:
            nodes.append(node)
        elif isinstance(node, ast.Assign) and any(
                isinstance(target, ast.Name) and target.id in assignments
                for target in node.targets):
            nodes.append(node)
    scope = {}
    exec(compile(ast.Module(body=nodes, type_ignores=[]), str(path), 'exec'), scope)
    return scope


def doc_prefix(text, line):
    lines = text.splitlines()
    j = line - 2
    while j >= 0 and (not lines[j].strip() or lines[j].startswith('omit ')):
        j -= 1
    if j < 0 or not lines[j].rstrip().endswith('-/'):
        return ''
    k = j
    while k >= 0 and '/--' not in lines[k]:
        k -= 1
    if k < 0:
        return ''
    doc = '\n'.join(lines[k:j + 1]).strip()[3:-2]
    return ' '.join(doc.split('**Proof sketch.**', 1)[0].split())


def global_map(sources, decls, parse_decls):
    result, all_names = {}, {}
    for path, raw in sorted(sources.items()):
        text = raw.decode('utf-8')
        parsed = parse_decls(text)
        for row in parsed:
            name = row['full']
            need(name not in all_names, 'Duplicate source FQN: ' + name + ' at '
                 + repr((all_names.get(name), path, row['line'])))
            all_names[name] = (path, row['line'])
        headers = decls(text)
        expected = {row['full'] for row in parsed if 'private' not in row['flags']}
        need(set(headers) == expected, 'Reviewed parsers disagree on public names in ' + path
             + ': ' + repr((sorted(expected - set(headers)), sorted(set(headers) - expected))))
        for name, (kind, line, header) in headers.items():
            need(name not in result, 'Duplicate public FQN: ' + name)
            prose = doc_prefix(text, line)
            result[name] = {'file': path, 'line': line, 'kind': kind,
                            'normalized_header': header, 'statement_prose_prefix': prose,
                            'header_sha256': sha(header.encode()),
                            'prose_prefix_sha256': sha(prose.encode())}
    return result


def current_paths(root):
    folder = root / PREFIX
    files = sorted(p for p in folder.rglob('*.lean') if p.is_file())
    files.append(root / FACADE)
    need(all(p.is_file() and not p.is_symlink() for p in files), 'Missing/symlink owner source')
    return sorted({p.relative_to(root).as_posix() for p in files})


def ledger_rows(paths, key='declarations'):
    rows = []
    for path in paths:
        value = json.loads(Path(path).read_text())
        rows.extend(value if isinstance(value, list) else value[key])
    return rows


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--root', default='.')
    ap.add_argument('--base', default=BASE)
    ap.add_argument('--freeze')
    ap.add_argument('--expected-frozen-count', type=int, default=670,
                    help='Historical M0 snapshot cardinality, not a current-source count')
    ap.add_argument('--moves', action='append', default=[], help='Explicit declaration relocation JSON')
    ap.add_argument('--prose-updates', action='append', default=[],
                    help='Optional exact old/new prose hashes plus approval_reference')
    ap.add_argument('--out', required=True, help='Fresh evidence directory')
    args = ap.parse_args()
    root, out = Path(args.root).resolve(), Path(args.out).resolve()
    need(not out.exists(), 'Choose a fresh output directory; existing evidence is preserved')
    freeze = args.freeze or (root / 'evidence/freeze/M0.txt').read_text().strip()
    freeze = git(root, 'rev-parse', '--verify', freeze + '^{commit}').decode().strip()
    head = git(root, 'rev-parse', 'HEAD').decode().strip()
    subprocess.run(['git', '-C', str(root), 'merge-base', '--is-ancestor', args.base, freeze], check=True)
    subprocess.run(['git', '-C', str(root), 'merge-base', '--is-ancestor', freeze, head], check=True)
    changed = git(root, 'diff', '--no-renames', '--name-only', '-z', args.base, freeze, '--')
    frozen_paths = sorted(p.decode() for p in changed.split(b'\0') if p and owned(p.decode()))
    need(frozen_paths, 'Frozen owner inventory is empty')
    now_paths = current_paths(root)
    need(now_paths, 'Current owner inventory is empty')
    frozen_sources = {path: git(root, 'show', freeze + ':' + path) for path in frozen_paths}
    now_sources = {path: (root / path).read_bytes() for path in now_paths}
    decl_tool = root / 'evidence/tools/seal/decls2.py'
    clash_tool = root / 'evidence/tools/clash/clash_scan.py'
    dscope = parser_functions(decl_tool, {'strip', 'decls'}, {'KW'})
    cscope = parser_functions(clash_tool, {'strip_code', 'parse_decls'},
                              {'KINDS', 'MODS', 'ATTR', 'DECL_RE', 'NAME_RE'})
    old = global_map(frozen_sources, dscope['decls'], cscope['parse_decls'])
    now = global_map(now_sources, dscope['decls'], cscope['parse_decls'])
    need(len(old) == args.expected_frozen_count,
         'Frozen global census differs from independent historical expected count: ' + str(len(old)))
    removed = sorted(set(old) - set(now))
    changed_headers = [name for name in old if name in now and
                       (old[name]['kind'], old[name]['normalized_header']) !=
                       (now[name]['kind'], now[name]['normalized_header'])]
    need(not removed, 'Frozen FQNs removed globally: ' + repr(removed))
    need(not changed_headers, 'Frozen kind/header changed: ' + repr(changed_headers))
    approved_prose = {}
    for row in ledger_rows(args.prose_updates, 'updates'):
        need(row['name'] not in approved_prose and row.get('approval_reference'),
             'Duplicate/unapproved prose exception')
        approved_prose[row['name']] = row
    changed_prose = [name for name in old if old[name]['statement_prose_prefix'] !=
                     now[name]['statement_prose_prefix']]
    need(set(changed_prose) == set(approved_prose), 'Prose changes/explicit exceptions differ: '
         + repr((changed_prose, sorted(approved_prose))))
    for name in changed_prose:
        row = approved_prose[name]
        need(row['old_sha256'] == old[name]['prose_prefix_sha256'] and
             row['new_sha256'] == now[name]['prose_prefix_sha256'], 'Prose exception hash differs')
    moves = {name: (old[name]['file'], now[name]['file']) for name in old
             if old[name]['file'] != now[name]['file']}
    approved_moves = {}
    for row in ledger_rows(args.moves):
        name, before, after = row['name'], row['old_file'], row['new_file']
        need(name in old and before == old[name]['file'], 'Move ledger has unknown/wrong frozen origin')
        if before == after:
            need(now[name]['file'] == after, 'Declared stationary item actually moved')
            continue
        need(name not in approved_moves, 'Duplicate move ledger name')
        approved_moves[name] = (before, after)
    need(moves == approved_moves, 'Actual/explicitly approved moves differ: '
         + repr((moves, approved_moves)))
    added = sorted(set(now) - set(old))
    need(all(now[name]['kind'] in {'theorem', 'lemma'} for name in added),
         'New non-theorem source declaration: ' + repr([name for name in added
            if now[name]['kind'] not in {'theorem', 'lemma'}]))
    # Retain and exactly reconcile the original PER-FILE report, never discard removals.
    union = sorted(set(frozen_paths) | set(now_paths))
    need(set(union) <= set(now_paths), 'Deleted owner file requires separate reviewed treatment')
    raw = subprocess.run(['python3', '-I', str(decl_tool), str(root), freeze, *union],
                         cwd=root, text=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    need(raw.returncode == 0 and not raw.stderr, 'Original per-file decls2 failed: ' + raw.stderr)
    categories = {'ADDED': [], 'REMOVED': [], 'CHANGED': []}
    for line in raw.stdout.splitlines():
        cells = line.split('\t')
        need(len(cells) >= 4 and cells[0] in categories, 'Unexpected decls2 output line: ' + line)
        categories[cells[0]].append(cells[2])
    need(not categories['CHANGED'], 'Per-file changed headers are never waived')
    need(Counter(categories['REMOVED']) == Counter(moves.keys()), 'Per-file removals not exactly approved moves')
    need(Counter(categories['ADDED']) == Counter([*moves, *added]),
         'Per-file additions not exactly moved or explicitly reported new theorem names')
    need(current_paths(root) == now_paths and all((root / path).read_bytes() == data
         for path, data in now_sources.items()), 'Current source changed during audit')
    summary = {'status': 'FROZEN_GLOBAL_HEADERS_AND_STATEMENT_PROSE_PASS',
               'mode': 'WORKTREE_CANDIDATE', 'base': args.base, 'freeze': freeze,
               'HEAD_at_capture': head, 'frozen_owners': len(frozen_paths),
               'current_owners': len(now_paths), 'frozen_headers': len(old),
               'current_headers': len(now), 'globally_removed': removed,
               'globally_changed_headers': changed_headers,
               'approved_prose_updates': changed_prose, 'moves': moves,
               'new_theorems_reported': added, 'new_helper_admission_reviewed': False,
               'qualification': 'Frozen preservation guard only. Additional theorem overlap/axiom '
                                'and milestone checks remain separate. Worktree bytes are not '
                                'claimed committed at HEAD; every exact source hash is bound.',
               'current_source_sha256': {path: sha(data) for path, data in now_sources.items()},
               'frozen_source_sha256': {path: sha(data) for path, data in frozen_sources.items()},
               'reviewed_tool_sha256': {'decls2': sha(decl_tool.read_bytes()),
                                       'clash_parser': sha(clash_tool.read_bytes())},
               'as_of': datetime.datetime.now(datetime.timezone.utc).isoformat()}
    out.mkdir(parents=True)
    (out / 'per-file-decls2.tsv').write_text(raw.stdout)
    (out / 'frozen-global-map.json').write_text(json.dumps(old, indent=2) + '\n')
    (out / 'current-global-map.json').write_text(json.dumps(now, indent=2) + '\n')
    (out / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n')
    print('GLOBAL_FREEZE_PASS', len(old), 'frozen;', len(now_paths), 'owners;',
          len(moves), 'approved moves;', len(added), 'new theorems separately reported')


if __name__ == '__main__':
    try:
        main()
    except (RuntimeError, OSError, ValueError, subprocess.CalledProcessError) as error:
        print('GLOBAL_FREEZE_FAIL', error, file=sys.stderr)
        raise SystemExit(1)
