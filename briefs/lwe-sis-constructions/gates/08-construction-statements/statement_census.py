"""Statement-only census using the existing campaign comment/namespace scanner.

Unlike the older proof-fill scanner, statement types here may contain outer lets.
Select the last outer assignment and retain standalone @[...] attributes as commands.
This is intentionally limited to this skeleton's rfl/by-sorry theorem bodies; it is
not a general Lean parser or a future proof-fill freezer. Historical tools stay fixed.
"""

from pathlib import Path
import re
import runpy


ROOT = Path(__file__).resolve().parents[4]
LEGACY = runpy.run_path(str(ROOT /
    'briefs/lwe-sis-constructions/fills/00-encodings/verify_freeze.py'))
STRIP, DECL = LEGACY['STRIP'], LEGACY['DECL']
COMMAND = re.compile(LEGACY['COMMAND'].pattern + r'|^@\[', re.M)


def proof_assignment(block):
    stack, assignments = [], []
    pairs = {'(': ')', '[': ']', '{': '}'}
    for index, char in enumerate(block):
        if char in pairs:
            stack.append(pairs[char])
        elif stack and char == stack[-1]:
            stack.pop()
        elif not stack and block.startswith(':=', index):
            assignments.append(index)
    assert assignments
    return assignments[-1]


def inspect(source):
    text = STRIP(source)
    starts = list(COMMAND.finditer(text))
    output, declarations, proofs, namespaces = [], [], {}, []
    output.append(text[:starts[0].start()] if starts else text)
    for index, start in enumerate(starts):
        stop = starts[index + 1].start() if index + 1 < len(starts) else len(text)
        block = text[start.start():stop]
        first = block.splitlines()[0]
        if first.startswith('namespace '):
            namespaces.append(first.split()[1])
        elif first == 'end' or first.startswith('end '):
            namespaces.pop()
        match = DECL.match(first)
        if match:
            kind, tail = match.groups()
            name = re.match(r'[^\s(:{]+', tail).group(0)
            full = '.'.join([*namespaces, name])
            declarations.append((kind, full))
            if kind in {'theorem', 'lemma'}:
                offset = proof_assignment(block)
                proof = ' '.join(block[offset + 2:].split())
                assert proof in {'rfl', 'by sorry'}, (full, proof)
                proofs[full] = proof
                block = block[:offset + 2] + ' <proof>\n'
        output.append(block)
    return ' '.join(''.join(output).split()), declarations, proofs
