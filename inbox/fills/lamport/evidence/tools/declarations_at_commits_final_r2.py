"""Inventory explicit declarations in immutable base/final Lean sources.

Run as python3 -I. Adapted from declarations_at_commits.py without replacing
that checkpoint tool or any checkpoint output. This performs no compilation,
proof-source writes or Git mutations. The output is created exclusively.
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
FINAL = '47ced271090f45918645c842cd358c5079092754'


def git(*args):
    return subprocess.check_output(['git', '-C', str(ROOT), *args])


def source(revision, path):
    result = subprocess.run(['git', '-C', str(ROOT), 'show', revision + ':' + path],
                            capture_output=True)
    if result.returncode:
        if b'does not exist' in result.stderr or b'exists on disk, but not in' in result.stderr:
            return None
        raise RuntimeError(result.stderr.decode())
    return result.stdout


def without_comments(text):
    # Keep line numbers; the grammar/quoted-source limitations are recorded below.
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
    for number, line in enumerate(without_comments((raw or b'').decode()).splitlines(), 1):
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


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--base', default=BASE)
    parser.add_argument('--head', default=FINAL)
    parser.add_argument('--output', default='new-declarations-final-r2.json')
    args = parser.parse_args()
    paths = git('diff', '--name-only', args.base, args.head, '--', '*.lean').decode().splitlines()
    files = {}
    totals = dict(changed_lean_files=len(paths), new_helper_paths=0,
                  explicit_declarations_base=0, explicit_declarations_final=0,
                  public_new_since_issue=0, private_new_since_issue=0,
                  removed_since_issue=0)
    for path in paths:
        raw = {label: source(revision, path) for label, revision in [('issue', args.base), ('final', args.head)]}
        decls = {label: declarations(text) for label, text in raw.items()}
        names = {label: {row['name'] for row in rows} for label, rows in decls.items()}
        if any(len(names[label]) != len(decls[label]) for label in names):
            raise RuntimeError('duplicate lexical names require review: ' + path)
        new = [row for row in decls['final'] if row['name'] not in names['issue']]
        item = dict(exists={label: text is not None for label, text in raw.items()},
                    source_sha256={label: hashlib.sha256(text).hexdigest() if text is not None else None for label, text in raw.items()},
                    explicit_declarations_base=decls['issue'],
                    explicit_declarations_final=decls['final'],
                    public_new_since_issue=[row for row in new if row['visibility'] == 'public'],
                    private_new_since_issue=[row for row in new if row['visibility'] == 'private'],
                    removed_since_issue=sorted(names['issue'] - names['final']))
        files[path] = item
        totals['new_helper_paths'] += raw['issue'] is None
        totals['explicit_declarations_base'] += len(decls['issue'])
        totals['explicit_declarations_final'] += len(decls['final'])
        for key in ['public_new_since_issue', 'private_new_since_issue', 'removed_since_issue']:
            totals[key] += len(item[key])
    origin = EVIDENCE / 'tools/declarations_at_commits.py'
    preserved = []
    for path in sorted(EVIDENCE.glob('new-declarations-checkpoint*.json')):
        preserved.append(dict(path=path.name, sha256=hashlib.sha256(path.read_bytes()).hexdigest()))
    payload = dict(issue_base=args.base, final_head=args.head,
                   tool=dict(path=str(Path(__file__).resolve()), sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
                             checkpoint_tool_preserved=dict(path=str(origin), sha256=hashlib.sha256(origin.read_bytes()).hexdigest())),
                   method='Explicit source declaration commands; namespace-qualified lexical names from immutable Git blobs; names compared per file.',
                   parser_limits=[
                       'Textual parser, not Lean elaboration: records supported line-leading declaration commands and simple namespace/section commands.',
                       'The comment stripper supports nested block/line comments but is not a Lean string, quoted-identifier or syntax-quotation parser.',
                       'Multiline or unusual command modifiers/attributes, macros, quotations and commands generated by run_cmd are not expanded.',
                       'Constructors, recursors, equation theorems, compiler auxiliaries and other elaborator-generated constants are omitted.',
                       'Private names are source lexical names, not Lean-mangled stored names; anonymous instances would be line-labeled.',
                       'A matching qualified name records retention, not unchanged statement, body, attributes or semantics; the independent source-integrity audit addresses original-source preservation.',
                       'The separate native all-stored-constant inventory/axiom census is authoritative for generated constants and axioms.'
                   ],
                   checkpoint_inventories_preserved=preserved,
                   compiler_run=False, git_mutations=False, totals=totals, files=files)
    destination = EVIDENCE / args.output
    with destination.open('x') as handle:
        handle.write(json.dumps(payload, indent=2) + '\n')
    print(json.dumps(dict(output=str(destination), **totals), indent=2))
    for path, item in files.items():
        print(path, 'new:', len(item['public_new_since_issue']), 'public,',
              len(item['private_new_since_issue']), 'private; removed:', len(item['removed_since_issue']))


if __name__ == '__main__':
    main()
