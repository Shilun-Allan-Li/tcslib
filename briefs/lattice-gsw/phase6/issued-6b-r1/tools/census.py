"""census.py (gsw-6b-statements staging, issued-6b-r1): a static reader census at the base, from git objects only.
Usage: census.py <repo> <rev> <listfile>.  Each list line is `<short name> <path relative to TCSlib/, no .lean>`
(a foreign definition that an r3 6b sketch or a 6b definition body is expected to read).  For each, print the
definition's line in its file and every theorem of that file whose last name component starts with
`<short>_`, compared case-insensitively (the reader naming convention: `_eq`, `_iff`, `_apply`, `_def`, case readers
such as `_nil`/`_cons`, and `simps` projections `_fst`/`_snd`), or MISSING when there is none.  Static name
matching only: the worker's census (brief, check 6) confirms each reader's statement and adds what this misses."""
import re, subprocess, sys
repo, rev, lst = sys.argv[1:4]
def show(p):
    return subprocess.run(['git', '-C', repo, 'show', f'{rev}:TCSlib/{p}.lean'], capture_output=True, text=True,
                          check=True).stdout.split('\n')
DEF = r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable)\s+)*(?:def|abbrev|structure|inductive|class)\s+'
THM = r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected)\s+)*theorem\s+(\S+)'
for line in open(lst):
    line = line.strip()
    if not line or line.startswith('#'): continue
    short, path = line.split()
    L = show(path)
    last = short.split('.')[-1]
    dl = [i for i, l in enumerate(L, 1) if re.match(DEF + r'(?:\S+\.)?' + re.escape(last) + r'\b', l)]
    rd = []
    for i, l in enumerate(L, 1):
        m = re.match(THM, l)
        if m:
            nm = m.group(1).split('.')[-1]
            if nm.lower().startswith(last.lower() + '_'):
                rd.append(f'{m.group(1)}:{i}')
    print(f'{short}\tTCSlib/{path}.lean:{",".join(map(str, dl)) or "?"}\t{" ".join(rd) if rd else "MISSING"}')
