"""Assemble the MIG-1 statement-gate unit from its part templates. Read-only on the worktree.

Usage: python3 -I build_unit.py <worktree> <parts-dir> <out.lean>

Each template line of the form
    -- @@verbatim <FileKey> <RenameKey|-> [--public] [--nodoc] [--stmt] <name> ...
is replaced by the verbatim text of the named declarations of that home file (scripts/mkshim.py),
with the rename map `RenameKey` of scripts/renames.json applied. Everything else is copied as is.
The templates (`*.lean`, or `*.lean.txt` as kept under `audits/`) are concatenated in file-name
order.
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


def main():
    wt, parts, out = sys.argv[1], sys.argv[2], sys.argv[3]
    renames = json.load(open(os.path.join(HERE, 'renames.json'), encoding='utf-8'))
    wraps = json.load(open(os.path.join(HERE, 'wraps.json'), encoding='utf-8'))
    chunks = []
    srcs = glob.glob(os.path.join(parts, '*.lean')) + glob.glob(os.path.join(parts, '*.lean.txt'))
    for p in sorted(srcs, key=os.path.basename):
        lines = open(p, encoding='utf-8').read().split('\n')
        res = []
        for l in lines:
            if l.startswith('-- @@verbatim '):
                w = l.split()[2:]
                fkey, rkey, rest = w[0], w[1], w[2:]
                rpath = '-'
                if rkey != '-':
                    rpath = os.path.join(HERE, '.rename-' + rkey + '.json')
                    json.dump(renames[rkey], open(rpath, 'w', encoding='utf-8'))
                txt = subprocess.run(
                    [sys.executable, '-I', os.path.join(HERE, 'mkshim.py'),
                     os.path.join(wt, FILES[fkey]), rpath] + rest,
                    check=True, capture_output=True, text=True).stdout.rstrip('\n')
                if rpath != '-':
                    os.remove(rpath)
                # wrap verbatim lines over 100 characters by the recorded line breaks
                # (scripts/wraps.json: whole-line replacements inside argument parentheses;
                # the identity check compares modulo whitespace)
                txt = '\n'.join(wraps.get(l, l) for l in txt.split('\n'))
                res.append(txt)
            else:
                res.append(l)
        chunks.append('\n'.join(res).rstrip('\n') + '\n')
    with open(out, 'w', encoding='utf-8') as f:
        f.write('\n'.join(chunks))


if __name__ == '__main__':
    main()
