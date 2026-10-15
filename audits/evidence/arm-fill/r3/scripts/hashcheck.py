"""Every hash-like token (7-40 hex characters, not part of a 64-character SHA-256) in the given
files must resolve to a git object whose full hash it prefixes. Read-only
(`git rev-parse --verify`). An all-digit token that resolves to no object is listed as a number,
not a failure. usage: python3 -I hashcheck.py <repo> <file>..."""
import re, subprocess, sys
repo, files = sys.argv[1], sys.argv[2:]
tok = re.compile(r'(?<![0-9A-Za-z])[0-9a-f]{7,40}(?![0-9A-Za-z])')
seen, bad = {}, 0
for f in files:
    for t in tok.findall(open(f, encoding='utf-8').read()):
        if t in seen: continue
        r = subprocess.run(['git', '-C', repo, 'rev-parse', '--verify', '--quiet', t + '^{object}'], capture_output=True, text=True)
        full = r.stdout.strip()
        ok = r.returncode == 0 and full.startswith(t)
        typ = subprocess.run(['git', '-C', repo, 'cat-file', '-t', full], capture_output=True, text=True).stdout.strip() if ok else '-'
        seen[t] = (ok, full, typ); bad += not ok and not t.isdigit()
for t, (ok, full, typ) in sorted(seen.items()):
    print(('OK  ' if ok else 'NUM ' if t.isdigit() else 'BAD ') + f'{t:<40} {full or "(unresolved)"} {typ}')
print(f'{len(seen)} distinct tokens in {len(files)} files; {bad} unresolved')
sys.exit(1 if bad else 0)
