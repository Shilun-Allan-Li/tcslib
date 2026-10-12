import sys, re, os, importlib.util
# usage: vendor.py <upstream 3sum-apsp root> <fixes.py> <out worktree> <module>...  (modules in dependency order)
# Writes TCSlib/Programs/... vendored files from [AFM26] with the recorded, listed modifications.
root, fixf, wt, mods = sys.argv[1], sys.argv[2], sys.argv[3], sys.argv[4:]
COMMIT = 'e1a4e6508154ea59f030480661590a9fe3018011'
spec = importlib.util.spec_from_file_location('fixes', fixf)
fx = importlib.util.module_from_spec(spec); spec.loader.exec_module(fx)

def upath(m):
    return 'EndStatement.lean' if m == 'EndStatement' else m.replace('.', '/') + '.lean'

def newmod(m):
    if m == 'EndStatement': return 'TCSlib.Programs.WordRAM.Basic'
    if m == 'ThreeSumApsp.Machine.Steps': return 'TCSlib.Programs.WordRAM.Steps'
    for a, b in (('ThreeSumApsp.Lang.', 'TCSlib.Programs.Light.'), ('ThreeSumApsp.Util.', 'TCSlib.Programs.Util.')):
        if m.startswith(a): return b + m[len(a):]
    raise SystemExit(f'unmapped module {m}')

COMPAT_NAMES = ['List.map_coe_finRange_eq_range', 'List.Pairwise.merge', 'Set.mem_ofPred_eq', '.merge hO']
own = set(mods)
written = []
for m in mods:
    src = open(os.path.join(root, upath(m)), encoding='utf-8').read()
    notes = []
    # 1. the word RAM only
    if m == 'EndStatement':
        cut = src.index('/-- `T(n) = O(n^r)`')
        src = src[:cut].rstrip('\n') + '\n\nend EndStatement\n'
        old = ('/-! Claims of the paper «Truly Subquadratic 3SUM and Truly Subcubic APSP via Triangles in Sparse '
               'Lopsided Graphs» (Josh\nAlman, Virginia Vassilevska Williams), about programs of a word RAM defined '
               'here. Imports nothing, proves nothing. -/')
        new = ('/-!\n# The word RAM\n\nThe word RAM of [AFM26] (`EndStatement.lean` there): `Instr`, the nine '
               'instructions of a program;\n`exec`, a run of a program within a step budget; and `loadWords`, the '
               'initial memory. Imports\nnothing, proves nothing.\n\n## References\n\n* [AFM26] anthropics/formal-math, '
               f'`3sum-apsp`, commit {COMMIT[:8]}, Apache-2.0.\n-/')
        assert src.count(old) == 1, 'EndStatement docstring'
        src = src.replace(old, new)
        notes.append('kept only the word RAM (`Instr`, `exec`, `loadWords`); dropped the paper\'s problems and claims, '
                     'and rewrote the module docstring accordingly')
    # 2. v4.25 proof repairs
    for a, b, why in fx.FIXES.get(m, []):
        assert src.count(a) == 1, (m, a[:50]); src = src.replace(a, b)
        notes.append(f'v4.25 proof repair ({why})')
    if 'with_unfolding_none' in src:
        src = src.replace('with_unfolding_none', 'with_reducible')
        notes.append('replaced the tactic combinator `with_unfolding_none`, absent in v4.25, by `with_reducible`')
    # 3. header, imports, module syntax
    hdr_end = src.index('-/\n') + 3
    header, body = src[:hdr_end], src[hdr_end:]
    assert header.startswith('/-\nCopyright (c) 2026 Anthropic, PBC.'), m
    imports, lines, stack = [], [], []
    for l in body.split('\n'):
        if l.strip() == 'module': continue
        mi = re.match(r'^(public )?import (\S+)\s*$', l)
        if mi:
            d = mi.group(2)
            assert d in own or d.startswith('Mathlib'), (m, d)
            imports.append(newmod(d) if d in own else d); continue
        if l.strip() in ('@[expose] public section', 'public section'): l = 'section'
        mn = re.match(r'^(namespace|section)\b\s*(\S*)', l); me = re.match(r'^end\b\s*(\S*)', l)
        if mn:
            if mn.group(1) == 'namespace': stack += mn.group(2).split('.')
            else: stack.append(mn.group(2))
        elif me and stack:
            for _ in range(max(1, len([x for x in me.group(1).split('.') if x]))): stack.pop()
        lines.append(l)
    body = '\n'.join(lines).rstrip('\n') + '\n'
    if stack:
        body += '\n'.join(('end ' + n).rstrip() for n in reversed(stack)) + '\n'
    # 4. renames: module names and paths in prose, then namespaces
    renamed = False
    for d in sorted(own - {'EndStatement'}, key=len, reverse=True):
        if d in body: body = body.replace(d, newmod(d)); renamed = True
    for a, b in (('ThreeSumApsp/Lang/', 'TCSlib/Programs/Light/'), ('ThreeSumApsp/Util/', 'TCSlib/Programs/Util/'),
                 ('ThreeSumApsp/Machine/', 'TCSlib/Programs/WordRAM/'),
                 ('ThreeSumApsp.WordRam', 'WordRAM'), ('EndStatement', 'WordRAM'), ('ThreeSumApsp', 'Light')):
        if a in body: body = body.replace(a, b); renamed = True
    if renamed:
        notes.append('namespaces `EndStatement` and `ThreeSumApsp.WordRam` renamed to `WordRAM`, and `ThreeSumApsp` '
                     'to `Light`, with module names and paths in comments updated')
    REF = ('## References\n\n* [AFM26] anthropics/formal-math, folder `3sum-apsp`, commit '
           f'{COMMIT[:8]}, Apache-2.0: the source of this file.\n')
    if '## References' not in body:
        k = body.find('/-!')
        if k >= 0:
            e = body.index('-/', k)
            body = body[:e].rstrip() + '\n\n' + REF + body[e:]
        else:
            title = newmod(m).split('.')[-1]
            body = (f'/-!\n# {title}\n\nA helper module of the vendored programming layer (see the file header).\n\n'
                    + REF + '-/\n\n' + body)
        notes.append('added a `## References` section citing [AFM26]')
    if any(c in body for c in COMPAT_NAMES):
        imports.append('TCSlib.Programs.Compat')
        notes.append('imports `TCSlib.Programs.Compat` for names that differ at our Mathlib pin')
    rel = newmod(m).replace('.', '/') + '.lean'
    vend = ('\nVendored from [AFM26] anthropics/formal-math (https://github.com/anthropics/formal-math), folder\n'
            f'`3sum-apsp`, file `{upath(m)}`, at commit {COMMIT} (2026-10-05).\n'
            'Local modifications (see policy.md §2, vendored code, and the repository NOTICE):\n'
            '* removed the Lean module-system syntax (`module`, `public import`, `@[expose] public section`)\n'
            '  for compatibility with our v4.25.0 toolchain;\n'
            f'* moved to `{rel}`, with imports remapped;\n'
            + ''.join(f'* {n};\n' for n in notes) +
            '* added the repository-standard `set_option` header.\n'
            'The remaining content is unchanged.\n')
    header = header[:-3].rstrip('\n') + '\n' + vend + '-/\n'
    opts = ('\nset_option maxHeartbeats 0\nset_option relaxedAutoImplicit false\nset_option autoImplicit false\n')
    out = header + '\n'.join(f'import {i}' for i in imports) + '\n' + opts + body.lstrip('\n').join(['\n', ''])
    p = os.path.join(wt, rel); os.makedirs(os.path.dirname(p), exist_ok=True)
    open(p, 'w', encoding='utf-8').write(out)
    written.append((newmod(m), rel, len(notes)))
for nm, rel, k in written: print(f'{nm}\t{rel}\t{k} notes')
