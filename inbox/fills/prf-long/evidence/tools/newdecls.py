#!/usr/bin/env python3
"""List the declarations added by the fill, with their full headers (keyword line to the `:=`,
`|` or `where` that begins the body), per changed or new file, in file order.
usage: newdecls.py REPO BASE_REV FILE..."""
import re, subprocess, sys
sys.path.insert(0, '/workspace/pltools')
repo, rev, files = sys.argv[1], sys.argv[2], sys.argv[3:]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure)\s+([^\s:({\[]+)')
def decls(text):
    L = text.split('\n'); out = []
    for i, l in enumerate(L):
        m = DECL.match(l)
        if not m: continue
        s = '\n'.join(L[i:i + 60]); depth = 0; k = 0; end = len(s)
        while k < len(s):
            c = s[k]
            if s.startswith('--', k):
                k = s.find('\n', k) if s.find('\n', k) >= 0 else len(s); continue
            if c in '([{⟨': depth += 1
            elif c in ')]}⟩': depth -= 1
            elif depth == 0 and (s.startswith(':=', k) or s.startswith('\n  |', k)
                                 or s.startswith('\n|', k) or s.startswith(' where', k)):
                end = k; break
            k += 1
        h = s[:end].rstrip()
        out.append((m.group(2), i + 1, h))
    return out
total = 0
for f in files:
    p = subprocess.run(['git', '-C', repo, 'show', f'{rev}:{f}'], capture_output=True, text=True)
    base = {n for n, _, _ in decls(p.stdout)} if p.returncode == 0 else set()
    new = [d for d in decls(open(f'{repo}/{f}').read()) if d[0] not in base]
    print(f'## {f}: {len(new)} new declarations\n')
    for n, ln, h in new:
        print(f'-- line {ln}\n{h}\n')
    total += len(new)
print(f'TOTAL {total} new declarations')
