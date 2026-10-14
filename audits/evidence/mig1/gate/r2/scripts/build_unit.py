"""Assemble the MIG-1 statement-gate unit from its part templates. Read-only on the worktree.

Usage: python3 -I build_unit.py <worktree> <parts-dir> <out.lean> [--expect N]

Each template line of the form
    -- @@verbatim <FileKey> <RenameKey|-> [--public] [--nodoc] [--stmt] <name> ...
is replaced by the verbatim text of the named declarations of that home file (scripts/mkshim.py),
with the rename map `RenameKey` of scripts/renames.json applied. Everything else is copied as is.
The templates (`*.lean`, or `*.lean.txt` as kept under `audits/`) are concatenated in file-name
order.

Round 2 (finding 2): the script refuses a missing parts directory, an empty template set, a
template set of another size than `--expect N`, a template that names both `X.lean` and
`X.lean.txt`, and a missing source file, all before writing anything; it assembles the whole
output in memory and replaces <out.lean> only after every directive has succeeded (`mkshim.py`
exits nonzero on an unknown declaration name), through a temporary file in the same directory.
The temporary rename maps carry the process id and are removed in every case.
"""
import glob
import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
FILES = {
    'Composition': 'TCSlib/Complexity/TuringMachine/Composition.lean',
    'Primitives': 'TCSlib/Complexity/TuringMachine/Build/Primitives.lean',
    'Loop': 'TCSlib/Complexity/TuringMachine/Build/Loop.lean',
    'Wrappers': 'TCSlib/Complexity/TuringMachine/Build/Wrappers.lean',
    'TimeConstructible': 'TCSlib/Complexity/ClassP/TimeConstructible.lean',
    'Encoding': 'TCSlib/Complexity/TuringMachine/Encoding.lean',
    'Simulation': 'TCSlib/Complexity/TuringMachine/Simulation.lean',
    'Catalog': 'TCSlib/Complexity/TuringMachine/Build/Catalog.lean',
    'H2Draft': 'audits/evidence/h2/StepBlockDraft.lean.txt',
}


def fail(msg):
    print(f'build_unit.py: {msg}', file=sys.stderr)
    sys.exit(2)


def main():
    args = sys.argv[1:]
    expect = None
    if '--expect' in args:
        i = args.index('--expect')
        expect = int(args[i + 1])
        args = args[:i] + args[i + 2:]
    if len(args) != 3:
        fail('usage: build_unit.py <worktree> <parts-dir> <out.lean> [--expect N]')
    wt, parts, out = args
    if not os.path.isdir(wt):
        fail(f'worktree {wt} missing')
    if not os.path.isdir(parts):
        fail(f'parts directory {parts} missing')
    srcs = glob.glob(os.path.join(parts, '*.lean')) + glob.glob(os.path.join(parts, '*.lean.txt'))
    if not srcs:
        fail(f'no templates (*.lean, *.lean.txt) in {parts}')
    keys = [os.path.basename(p).replace('.lean.txt', '.lean') for p in srcs]
    if len(set(keys)) != len(keys):
        fail(f'a template occurs as both .lean and .lean.txt in {parts}')
    if expect is not None and len(srcs) != expect:
        fail(f'{len(srcs)} templates in {parts}, expected {expect}')
    for k, rel in FILES.items():
        if not os.path.isfile(os.path.join(wt, rel)):
            fail(f'source file {rel} ({k}) missing from the worktree')
    renames = json.load(open(os.path.join(HERE, 'renames.json'), encoding='utf-8'))
    wraps = json.load(open(os.path.join(HERE, 'wraps.json'), encoding='utf-8'))
    chunks, temps, directives = [], [], 0
    try:
        for p in sorted(srcs, key=os.path.basename):
            lines = open(p, encoding='utf-8').read().split('\n')
            res = []
            for l in lines:
                if l.startswith('-- @@verbatim '):
                    directives += 1
                    w = l.split()[2:]
                    fkey, rkey, rest = w[0], w[1], w[2:]
                    if fkey not in FILES:
                        fail(f'{os.path.basename(p)}: unknown file key {fkey}')
                    rpath = '-'
                    if rkey != '-':
                        if rkey not in renames:
                            fail(f'{os.path.basename(p)}: unknown rename key {rkey}')
                        rpath = os.path.join(HERE, f'.rename-{rkey}-{os.getpid()}.json')
                        temps.append(rpath)
                        json.dump(renames[rkey], open(rpath, 'w', encoding='utf-8'))
                    r = subprocess.run(
                        [sys.executable, '-I', os.path.join(HERE, 'mkshim.py'),
                         os.path.join(wt, FILES[fkey]), rpath] + rest,
                        capture_output=True, text=True)
                    if r.returncode != 0 or not r.stdout.strip():
                        fail(f'{os.path.basename(p)}: mkshim.py failed ({r.returncode}): '
                             f'{r.stderr.strip()[:300]}')
                    txt = r.stdout.rstrip('\n')
                    # wrap verbatim lines over 100 characters by the recorded line breaks
                    # (scripts/wraps.json: whole-line replacements inside argument parentheses;
                    # the identity check compares modulo whitespace)
                    txt = '\n'.join(wraps.get(x, x) for x in txt.split('\n'))
                    res.append(txt)
                else:
                    res.append(l)
            chunks.append('\n'.join(res).rstrip('\n') + '\n')
    finally:
        for t in temps:
            if os.path.exists(t):
                os.remove(t)
    text = '\n'.join(chunks)
    if not text.strip():
        fail('assembled output is empty')
    tmp = out + f'.tmp-{os.getpid()}'
    with open(tmp, 'w', encoding='utf-8') as f:
        f.write(text)
    os.replace(tmp, out)
    print(f'build_unit.py: {len(srcs)} templates, {directives} verbatim directives, '
          f'{text.count(chr(10))} lines -> {out}')


if __name__ == '__main__':
    main()
