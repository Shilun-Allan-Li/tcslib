"""List every public theorem/lemma whose statement (up to `:=`) mentions a given identifier,
at a given git revision (read-only `git show`/`git ls-tree`). Usage: statements.py <repo> <rev> <ident>..."""
import re, subprocess, sys
repo, rev, idents = sys.argv[1], sys.argv[2], sys.argv[3:]
files = subprocess.run(["git", "-C", repo, "ls-tree", "-r", "--name-only", rev, "TCSlib"],
                       capture_output=True, text=True, check=True).stdout.split()
files = [f for f in files if f.endswith(".lean")]
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*((?:private|protected|noncomputable)\s+)*(theorem|lemma)\s+(\S+)", re.M)
def strip(src):
    out, i, d = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i): d += 1; i += 2; continue
        if src.startswith("-/", i) and d: d -= 1; i += 2; continue
        if d == 0: out.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0] for l in "".join(out).splitlines())
pats = {k: re.compile(r"(?<![A-Za-z0-9_'.])(?:[A-Za-z0-9_']+\.)*" + re.escape(k) + r"(?![A-Za-z0-9_'])") for k in idents}
for f in files:
    src = subprocess.run(["git", "-C", repo, "show", f"{rev}:{f}"], capture_output=True, text=True).stdout
    s = strip(src)
    ms = list(DECL.finditer(s))
    for m in ms:
        if m.group(1) and "private" in m.group(1):
            continue
        rest = s[m.end():]
        stmt = rest[: rest.find(":=")] if ":=" in rest else rest[:400]
        hits = [k for k, p in pats.items() if p.search(stmt) or p.search(m.group(3))]
        if hits:
            line = s[: m.start()].count("\n") + 1
            print(f"{f}:{line}: {m.group(3)} [{','.join(hits)}] :: {' '.join(stmt.split())[:300]}")
