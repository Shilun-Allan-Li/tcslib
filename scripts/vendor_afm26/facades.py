import os, re, sys
# usage: facades.py <worktree>: write the TCSlib/Programs facades (Contents from each child's `# Title`).
wt = sys.argv[1]; base = f'{wt}/TCSlib/Programs'
HDR = ('/-\nCopyright (c) 2026 Seyoon Ragavan. All rights reserved.\n'
       'Released under Apache 2.0 license as described in the file LICENSE.\nAuthors: Seyoon Ragavan\n-/\n')
REF = ('## References\n\n* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit e1a4e650, Apache-2.0: '
       'the source of the vendored files (see each file\'s header and the repository NOTICE).\n')
def title(path):
    t = open(path, encoding='utf-8').read()
    m = re.search(r'/-!\s*\n?#\s+(.+)', t)
    return m.group(1).strip() if m else os.path.basename(path)[:-5]
def mod(path): return os.path.relpath(path, wt)[:-5].replace('/', '.')
def facade(path, heading, intro, children):
    lines = [f'import {mod(c)}' for c in children]
    contents = '\n'.join(f'* `{mod(c)}`: {title(c)}' for c in children)
    open(path, 'w', encoding='utf-8').write(HDR + '\n'.join(lines) + '\n\n/-!\n# ' + heading + '\n\n' + intro +
        '\n\n## Contents\n\n' + contents + '\n\n' + REF + '-/\n')
def kids(d): return sorted(f'{d}/{f}' for f in os.listdir(d) if f.endswith('.lean'))
facade(f'{base}/Util.lean', 'Programs: general facts', 'Lists, sums, digits, indices and counting facts that the language and its routines use.', kids(f'{base}/Util'))
facade(f'{base}/WordRAM.lean', 'Programs: the word RAM', 'The word RAM of [AFM26]: its nine instructions, runs, and the facts about runs that compiled code needs.', kids(f'{base}/WordRAM'))
def tree(d): return sorted(os.path.join(r, f) for r, _, fs in os.walk(d) for f in fs if f.endswith('.lean'))
facade(f'{base}/Light.lean', 'Programs: the light language',
       'A small imperative language with procedures and recursion; its program logic (`Ends`, `Meets`) and '
       'tactics; verified routines (`Lib/`: copying, merge, counting and radix sorting, logarithms, powers, modular '
       'reduction, square roots and others); and the compiler to the word RAM (`Compiler/`, with '
       '`compileProgram_correct`: a run of `c` steps becomes a run of `startCost + stepsPerStep * c` steps).',
       tree(f'{base}/Light'))
facade(f'{wt}/TCSlib/Programs.lean', 'Programs',
       'The programming layer (design `machine-library-design.md` §15): the light language and its logic, the word '
       'RAM, and the compiler between them, vendored from [AFM26]; and the compatibility names for our Mathlib pin. '
       'Every module of the area is imported directly; the topic facades are `TCSlib.Programs.Util`, '
       '`TCSlib.Programs.WordRAM` and `TCSlib.Programs.Light`.',
       [f'{base}/Compat.lean', f'{base}/Util.lean', f'{base}/WordRAM.lean', f'{base}/Light.lean'] + tree(f'{base}/Util') + tree(f'{base}/WordRAM') + tree(f'{base}/Light'))
print('facades written')
