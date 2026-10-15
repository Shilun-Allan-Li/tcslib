"""Policy checks (policy.md §1-3) over given Lean files.
usage: python3 -I policy.py <root> <file> [<file> ...]
Per file: lines; module docstring sections (# Title, ## Main definitions, ## Main results,
## References); header block and the three standard options; lines over 100 characters
(counted in Unicode characters); public declarations without a docstring (instances
exempt); proofs longer than 20 non-blank code lines whose docstring has no `Proof sketch`;
the citation tags used.
"""
import os, re, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from freeze2 import parse, TAG

root, files = sys.argv[1], sys.argv[2:]
OPTS = ['set_option maxHeartbeats 0', 'set_option relaxedAutoImplicit false',
        'set_option autoImplicit false']
tot = dict(files=0, lines=0, long=0, nodoc=0, nosketch=0, nosketch_pub=0, pub=0, priv=0)
long_lines, nodoc, nosketch, headers, sizes, tagsum, untagged_bold = [], [], [], [], [], {}, []
for f in files:
    raw = open(os.path.join(root, f), encoding='utf-8').read()
    lines = raw.split('\n')
    if lines and lines[-1] == '': lines = lines[:-1]
    tot['files'] += 1; tot['lines'] += len(lines); sizes.append((len(lines), f))
    for i, l in enumerate(lines, 1):
        if len(l) > 100: long_lines.append((f, i, len(l)))
    m = re.search(r'/-!(.*?)-/', raw, re.S)
    md = m.group(1) if m else ''
    secs = {k: (k in md) for k in ('\n# ', '## Main definitions', '## Main results', '## References')}
    if md.lstrip().startswith('# '): secs['\n# '] = True
    hdr = raw.startswith('/-\nCopyright')
    opts = all(o in raw for o in OPTS)
    headers.append((f, hdr, opts, secs))
    ds = parse(os.path.join(root, f))
    for n, d in ds.items():
        if d['private']: tot['priv'] += 1
        else: tot['pub'] += 1
        if not d['private'] and d['kind'] != 'instance' and not d['doc']:
            nodoc.append((f, d['line'], d['kind'], n))
        body = [l for l in d['body'].split('\n') if l.strip()]
        if d['kind'] in ('theorem', 'lemma') and len(body) > 20 and 'proof sketch' not in d['doc'].lower():
            nosketch.append((f, d['line'], n, len(body), d['private']))
        for t in TAG.finditer(d['doc']):
            tagsum.setdefault(t.group(1), 0); tagsum[t.group(1)] += 1
        if (not d['private'] and d['kind'] in ('theorem', 'lemma') and d['doc'].startswith('/-- **')
                and not TAG.search(d['doc'])):
            untagged_bold.append((f, d['line'], n))
print(f"files {tot['files']}, lines {tot['lines']}, public {tot['pub']}, private {tot['priv']}")
print('\n## Header and module docstring (copyright block / 3 options / # Title / Main definitions / Main results / References)')
for f, hdr, opts, secs in headers:
    miss = [k.strip() for k, v in secs.items() if not v]
    flag = ('' if hdr else ' NO-COPYRIGHT') + ('' if opts else ' MISSING-OPTIONS') + (' missing: ' + ', '.join(miss) if miss else '')
    if flag: print(f'  {f}:{flag}')
print('  (files not listed have all six)')
print(f'\n## Lines over 100 characters: {len(long_lines)} in {len({x[0] for x in long_lines})} files')
for f, i, n in long_lines: print(f'  {f}:{i}  {n} chars')
print(f'\n## Public declarations (instances exempt) without a docstring: {len(nodoc)}')
for x in nodoc: print('  %s:%d  %s %s' % x)
print(f'\n## Theorems/lemmas with more than 20 non-blank code lines and no "Proof sketch" in the docstring: {len(nosketch)} '
      f'({sum(1 for x in nosketch if not x[4])} public, {sum(1 for x in nosketch if x[4])} private)')
for f, i, n, k, p in sorted(nosketch, key=lambda x: -x[3]): print(f'  {f}:{i}  {n}  ({k} lines{", private" if p else ""})')
print(f'\n## Citation tags used in declaration docstrings: {dict(sorted(tagsum.items()))}')
print(f'\n## Public theorems with a bold "result" headline (/-- **...) and no [Tag, …] citation: {len(untagged_bold)}')
for x in untagged_bold: print('  %s:%d  %s' % x)
print('\n## File sizes (report only; size is never a reason to split)')
for n, f in sorted(sizes, reverse=True): print(f'  {n:5d}  {f}')
