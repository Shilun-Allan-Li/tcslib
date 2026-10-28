"""Build TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean from its base blob and the dev
modules: the dev declarations go, `private`, into region (b) (after `qy_query_of_main`, before the
target's docstring); region (d), the target's `**Implementation status.**` paragraph, and region
(c), the body after the `suffices`, are replaced by the given texts.

Usage: python3 -I land.py <status-file> <body-file> <dev module> ...
"""
import re, subprocess, sys
ROOT = '/home/user/tcslib'
PATH = 'TCSlib/Complexity/Diagonalization/NTimeDiagonalizer.lean'
BASE = '43fe918f2b7612b46d6b1bd6d4201651f7243430'
status = open(sys.argv[1], encoding='utf-8').read().rstrip('\n')
body = open(sys.argv[2], encoding='utf-8').read().rstrip('\n')
mods = sys.argv[3:]
base = subprocess.run(['git', '-C', ROOT, 'show', f'{BASE}:{PATH}'], capture_output=True,
                      text=True, check=True).stdout
DECL = re.compile(r'^(theorem|lemma|def|abbrev|inductive|structure|instance)\b')
region = []
for m in mods:
    src = open(f'{ROOT}/evidence/dev/{m}.lean', encoding='utf-8').read().split('\n')
    out = []
    for l in src:
        if l.endswith(' -- dev'):
            continue
        if l.startswith('import ') or l.startswith('set_option ') or \
                l == 'namespace Turing.NTimeDiag' or l == 'end Turing.NTimeDiag':
            continue
        if DECL.match(l):
            l = 'private ' + l
        out.append(l)
    text = '\n'.join(out).strip('\n')
    region.append(text)
region_text = '\n\n'.join(region)
anchor = "/-- **The stage query in linear time** (C1-E;"
i = base.index(anchor)
pre, post = base[:i], base[i:]
# region (d): the Implementation status paragraph, up to the docstring's end
j = post.index("**Implementation status.**")
k = post.index("-/\ntheorem exists_queryTM")
post = post[:j] + status + " -/\ntheorem exists_queryTM" + post[k + len("-/\ntheorem exists_queryTM"):]
# region (c): the body after the suffices block, i.e. the line `  sorry` before exists_diagonalizer
m = post.index("    exact qy_query_of_main hg hM\n")
m2 = post.index("\n", post.index("  sorry", m))
post = post[:m + len("    exact qy_query_of_main hg hM\n")] + body + post[m2:]
new = pre.rstrip('\n') + '\n\n' + region_text + '\n\n' + post
open(f'{ROOT}/{PATH}', 'w', encoding='utf-8').write(new)
print(f"landed {len(mods)} modules; file has {new.count(chr(10))} lines")
