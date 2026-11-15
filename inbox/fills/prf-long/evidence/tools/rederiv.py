#!/usr/bin/env python3
"""For every base declaration of the given files: whether its text (docstring excluded) changed
between BASE_REV and the working tree, and the new proof in one line (whitespace collapsed,
cut at 160 characters). usage: rederiv.py REPO BASE_REV FILE..."""
import re, subprocess, sys
repo, rev, files = sys.argv[1], sys.argv[2], sys.argv[3:]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure)\s+([^\s:({\[]+)')
STOP = re.compile(r'^(/--|/-!|omit|section|end|namespace|variable|open|@\[|' + DECL.pattern[1:] + ')')
def blocks(text):
    L = text.split('\n'); out = {}
    for i, l in enumerate(L):
        m = DECL.match(l)
        if not m: continue
        j = i + 1
        while j < len(L) and not (L[j] and not L[j][0].isspace() and STOP.match(L[j])):
            j += 1
        out[m.group(2)] = '\n'.join(L[i:j]).rstrip()
    return out
for f in files:
    b = blocks(subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True,
                              text=True).stdout)
    n = blocks(open(f'{repo}/{f}').read())
    print(f'## {f}')
    for k in b:
        if k not in n: print(f'MISSING {k}'); continue
        if b[k] == n[k]: print(f'same     {k}'); continue
        s = n[k]; i = -1; d = 0
        for p, c in enumerate(s):
            if c in '([{⟨': d += 1
            elif c in ')]}⟩': d -= 1
            elif d == 0 and s.startswith(':=', p): i = p; break
        if i < 0: i = max(s.find('\n  |'), s.find('\n|'))
        body = re.sub(r'\s+', ' ', s[i:] if i >= 0 else s)[:160]
        print(f'CHANGED  {k}\t{body}')
