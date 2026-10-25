"""subst_hashes.py FILE...: replace ⟨REV:spec⟩ by `git rev-parse spec` (full) and ⟨REV8:spec⟩ by
its first 8 hex digits, and ⟨SHA256:path⟩ by the file's SHA-256, checking every object with
`git cat-file -t`. Then list every remaining 7-40 hex-digit word and check that each names a git
object (`git cat-file -t`), or report it for manual classification (SHA-256 sums, etc.)."""
import hashlib, re, subprocess, sys
def rev(spec):
    h = subprocess.run(['git', 'rev-parse', '--verify', spec], capture_output=True, text=True, check=True).stdout.strip()
    subprocess.run(['git', 'cat-file', '-t', h], capture_output=True, text=True, check=True)
    return h
TOK = re.compile(r'⟨(REV|REV8|SHA256):([^⟩]+)⟩')
for p in sys.argv[1:]:
    s = open(p, encoding='utf-8').read()
    def sub(m):
        kind, spec = m.group(1), m.group(2)
        if kind == 'SHA256':
            return hashlib.sha256(open(spec, 'rb').read()).hexdigest()
        h = rev(spec)
        return h if kind == 'REV' else h[:8]
    n = len(TOK.findall(s))
    s2 = TOK.sub(sub, s)
    if s2 != s: open(p, 'w', encoding='utf-8').write(s2)
    unknown = []
    for w in sorted(set(re.findall(r'(?<![0-9a-zA-Z])[0-9a-f]{7,40}(?![0-9a-zA-Z])', s2))):
        if not re.search(r'[a-f]', w) or not re.search(r'[0-9]', w): continue
        r = subprocess.run(['git', 'cat-file', '-t', w], capture_output=True, text=True)
        if r.returncode != 0: unknown.append(w)
    print(f'{p}: {n} tokens replaced; hex words not naming a git object: {unknown or "none"}')
