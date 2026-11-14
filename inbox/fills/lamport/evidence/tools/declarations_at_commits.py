"""List explicit source declarations at the frozen Lamport checkpoints.

Run with python3 -I. This is a textual source inventory, not a substitute for
the separate stored-constant/axiom census. It never writes proof sources.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path('/private/tmp/tcslib-lamport-01a1d88f/proof')
EVIDENCE = Path('/private/tmp/tcslib-lamport-01a1d88f/delivery/lamport/evidence')
BASE = 'eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9'
CP1 = '09ac6b6c8c7f5997928ee5dfb4f18984ba2709b5'
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--checkpoint2', default='11cc4e54fb63bb1c6310e90e6fbaa07e7031fb07')
parser.add_argument('--output', default='new-declarations-checkpoint2.json')
args = parser.parse_args()
CP2 = args.checkpoint2


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def source(revision, path):
    result = subprocess.run(['git', '-C', str(ROOT), 'show', revision + ':' + path],
                            capture_output=True)
    if result.returncode:
        if b'does not exist' in result.stderr or b'exists on disk, but not in' in result.stderr:
            return b''
        raise RuntimeError(result.stderr.decode())
    return result.stdout


def without_comments(text):
    chars, depth, index = list(text), 0, 0
    while index < len(text):
        if text.startswith('/-', index):
            depth += 1
            width = 2
        elif depth and text.startswith('-/', index):
            depth -= 1
            width = 2
        elif depth:
            width = 1
        elif text.startswith('--', index):
            end = text.find('\n', index)
            width = (len(text) if end < 0 else end) - index
        else:
            index += 1
            continue
        for k in range(index, index + width):
            if chars[k] != '\n':
                chars[k] = ' '
        index += width
    return ''.join(chars)


PATTERN = re.compile(
    r'^(?:@\[[^\]]*\]\s*)?'
    r'(?P<modifiers>(?:(?:private|protected|noncomputable|nonrec|unsafe|partial)\s+)*)'
    r'(?P<kind>theorem|lemma|def|abbrev|instance|structure|class|inductive|opaque|axiom)\b'
    r'\s*(?P<name>[^\s(:{]*)')


def declarations(raw):
    namespace, stack, rows = '', [], []
    for number, line in enumerate(without_comments(raw.decode()).splitlines(), 1):
        line = line.strip()
        opened = re.fullmatch(r'(namespace|section)(?:\s+(\S+))?', line)
        if opened:
            kind, name = opened.groups()
            stack.append(namespace)
            if kind == 'namespace':
                namespace = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(filter(None, [namespace, name]))
            continue
        if re.fullmatch(r'end(?:\s+\S+)?', line):
            if stack:
                namespace = stack.pop()
            continue
        match = PATTERN.match(line)
        if not match:
            continue
        name, kind, modifiers = match['name'], match['kind'], match['modifiers'].split()
        name = name or f'<anonymous {kind} at line {number}>'
        full = name.removeprefix('_root_.') if name.startswith('_root_.') else '.'.join(filter(None, [namespace, name]))
        rows.append(dict(name=full, source_name=name, kind=kind, line=number,
                         visibility='private' if 'private' in modifiers else 'public',
                         modifiers=modifiers))
    return rows


paths = git('diff', '--name-only', BASE, CP2, '--', '*.lean').decode().splitlines()
files = {}
totals = dict(public_since_issue=0, private_since_issue=0,
              public_since_checkpoint1=0, private_since_checkpoint1=0)
for path in paths:
    raw = {label: source(revision, path) for label, revision in [('issue', BASE), ('checkpoint1', CP1), ('checkpoint2', CP2)]}
    decls = {label: declarations(text) for label, text in raw.items()}
    names = {label: {row['name'] for row in rows} for label, rows in decls.items()}
    item = dict(source_sha256={label: hashlib.sha256(text).hexdigest() if text else None for label, text in raw.items()},
                explicit_declarations_checkpoint2=len(decls['checkpoint2']))
    for comparison, earlier in [('since_issue', 'issue'), ('since_checkpoint1', 'checkpoint1')]:
        new = [row for row in decls['checkpoint2'] if row['name'] not in names[earlier]]
        for visibility in ['public', 'private']:
            key = visibility + '_' + comparison
            item[key] = [row for row in new if row['visibility'] == visibility]
            totals[key] += len(item[key])
        item['removed_' + comparison] = sorted(names[earlier] - names['checkpoint2'])
    files[path] = item

cp1_path = EVIDENCE / 'new-declarations-checkpoint1.json'
payload = dict(issue_base=BASE, checkpoint1=CP1, checkpoint2=CP2,
               method='Explicit source declaration names, namespace-qualified; compare immutable Git sources. Private lexical names are not Lean-mangled stored names. Generated constants are covered by the separate runtime census.',
               checkpoint1_inventory_preserved=dict(path=cp1_path.name,
                   sha256=hashlib.sha256(cp1_path.read_bytes()).hexdigest()),
               totals=totals, files=files)
destination = EVIDENCE / args.output
assert not destination.exists(), 'preserve earlier inventory: ' + str(destination)
destination.write_text(json.dumps(payload, indent=2) + '\n')
print(json.dumps(totals, indent=2))
for path, item in files.items():
    print(path, 'new in checkpoint2:', len(item['public_since_checkpoint1']), 'public,', len(item['private_since_checkpoint1']), 'private')
