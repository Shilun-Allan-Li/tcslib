"""Shared helpers of the dedup payback landing pipeline (standard library only; read-only on
the base export). Every text edit made through this module is asserted: `sub` requires the
stated number of occurrences, `delete_decl` requires a unique declaration, `d1_rewrite` checks
its occurrence count.

The declaration cutter is the B6 gate's (`audits/evidence/b6hosts/gate/scripts/freeze.py`) and
the declaration scanner the MIG-1 gate's (`audits/evidence/mig1/gate/scripts/decls.py`), both
executed from their source text in the base export, unchanged (no bytecode is written).
"""
import hashlib
import os
import re
import subprocess
import sys
import tempfile
import types

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
L = os.path.dirname(HERE)
BASE = os.path.join(L, "work", "base")
TREE = os.path.join(L, "tree")
S = os.path.dirname(L)
REPO = "/Users/seyoonr/phd_experiments/tcslib"
BRANCH = "origin/complexity/arora-barak-ch3-4"
C = "TCSlib/Complexity/"
SC = C + "SpaceComplexity/"


def rd(p):
    with open(p, encoding="utf-8") as f:
        return f.read()


def wr(p, s):
    os.makedirs(os.path.dirname(p) or ".", exist_ok=True)
    with open(p, "w", encoding="utf-8") as f:
        f.write(s)


def sha(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def _load(name, rel):
    p = os.path.join(BASE, rel)
    m = types.ModuleType(name)
    m.__file__ = p
    exec(compile(rd(p), p, "exec"), m.__dict__)
    return m


declcut = _load("declcut", "audits/evidence/b6hosts/gate/scripts/freeze.py")
gdecls = _load("gdecls", "audits/evidence/mig1/gate/scripts/decls.py")

# ------------------------------------------------------------------ asserted text edits


def sub(text, old, new, n, what):
    """Replace `old` by `new`; `old` must occur exactly `n` times."""
    k = text.count(old)
    assert k == n, f"{what}: expected {n} occurrence(s), found {k}: {old[:100]!r}"
    return text.replace(old, new)


IDENT = re.compile(r"(?:[^\W\d]|_)[\w'!?]*(?:\.(?:[^\W\d]|_)[\w'!?]*)*")


def token_count(text, name):
    return sum(1 for m in IDENT.finditer(text) for p in m.group(0).split(".") if p == name)


def blank_comments(src):
    """Comments replaced by spaces (newlines kept), so offsets and lines are preserved."""
    return declcut.split_comments(src)[0]


D1_OLD = "InWin N "
D1_NEW = "Cfg.InWindow "


def d1_rewrite(text, n_code, n_comment, what):
    """D1's token rewrite: every code occurrence of `InWin N <radius> <cfg>` becomes
    `Cfg.InWindow <radius> <cfg>` (the same argument order; `Turing.Cfg.InWindow` takes the
    radius and the configuration explicitly). Comments are not rewritten here. The number of
    code occurrences and of comment occurrences of the token `InWin` are both asserted."""
    code = blank_comments(text)
    pat = re.compile(r"(?<![A-Za-z0-9_.'])InWin N ")
    hits = [m.start() for m in pat.finditer(code)]
    assert len(hits) == n_code, f"{what}: {len(hits)} code occurrences of `InWin N `, expected {n_code}"
    allc = token_count(code, "InWin")
    assert allc == n_code, f"{what}: {allc} code tokens InWin, expected {n_code}"
    comm = token_count(text, "InWin") - allc
    assert comm == n_comment, f"{what}: {comm} comment tokens InWin, expected {n_comment}"
    out, last = [], 0
    for h in hits:
        out.append(text[last:h])
        out.append(D1_NEW)
        last = h + len(D1_OLD)
    out.append(text[last:])
    return "".join(out)


def d1_private(text, n_code):
    """D1 in ConfigGraph: the code uses `InWindow s <cfg>` of the deleted private predicate
    become `Cfg.InWindow s <cfg>` (the same argument order). Count asserted."""
    code = blank_comments(text)
    pat = re.compile(r"(?<![A-Za-z0-9_.'])InWindow s ")
    hits = [m.start() for m in pat.finditer(code)]
    assert len(hits) == n_code, f"ConfigGraph: {len(hits)} code uses of `InWindow s `"
    out, last = [], 0
    for h in hits:
        out += [text[last:h], "Cfg.InWindow s "]
        last = h + len("InWindow s ")
    out.append(text[last:])
    return "".join(out)


def scan_text(text, tmpdir):
    os.makedirs(tmpdir, exist_ok=True)
    fd, p = tempfile.mkstemp(suffix=".lean", dir=tmpdir)
    os.close(fd)
    try:
        wr(p, text)
        ds, lines = gdecls.scan(p)
    finally:
        os.remove(p)
    return ds, lines


def locate(text, name, tmpdir, kind=None):
    """(doc_start, decl_line, end) as 0-based line indices (end inclusive) of the unique
    declaration `name` (as written after the keyword); doc_start is the line of the `/--`
    opening the docstring that ends right before it (or decl_line if there is none). An
    attribute line (`@[...]`) or `variable (...) in` / `open ... in` line directly above the
    docstring or the declaration is included in the span."""
    ds, lines = scan_text(text, tmpdir)
    hit = [d for d in ds if d["name"] == name and (kind is None or d["kind"] == kind)]
    assert len(hit) == 1, f"declaration {name}: {len(hit)} matches"
    d = hit[0]
    s = d["line"] - 1
    doc = s
    if s > 0 and lines[s - 1].rstrip().endswith("-/"):
        k = s - 1
        while k >= 0 and not lines[k].lstrip().startswith("/--"):
            k -= 1
        assert k >= 0, f"{name}: docstring start not found"
        doc = k
    while doc > 0 and (re.match(r"^(variable .* in|open .* in|set_option .* in)$", lines[doc - 1])):
        doc -= 1
    return doc, s, d["end"] - 1, lines


def delete_decl(text, name, tmpdir, kind=None):
    """Remove the unique declaration `name` with its docstring and one following blank line."""
    doc, s, e, ls = locate(text, name, tmpdir, kind)
    k = e + 1
    if k < len(ls) and not ls[k].strip():
        k += 1
    return "\n".join(ls[:doc] + ls[k:])


def decl_text(text, name, tmpdir, with_doc=True, kind=None):
    doc, s, e, ls = locate(text, name, tmpdir, kind)
    return "\n".join(ls[doc if with_doc else s:e + 1])


def make_public(text, name, tmpdir, kind=None):
    """Drop `private` from the declaration line of the unique declaration `name`."""
    doc, s, e, ls = locate(text, name, tmpdir, kind)
    line = ls[s]
    m = re.match(r"^((?:@\[[^\]]*\]\s*)?)private (.*)$", line)
    assert m, f"{name}: not private: {line!r}"
    ls[s] = m.group(1) + m.group(2)
    return "\n".join(ls)


def strip_comments(text):
    out, depth, j = [], 0, 0
    while j < len(text):
        if depth > 0:
            if text.startswith("/-", j):
                depth += 1; j += 2; continue
            if text.startswith("-/", j):
                depth -= 1; j += 2; continue
            j += 1; continue
        if text.startswith("/-", j):
            depth += 1; j += 2; continue
        if text.startswith("--", j):
            k = text.find("\n", j)
            j = len(text) if k < 0 else k
            continue
        out.append(text[j]); j += 1
    return "".join(out)


def code_norm(text):
    """Comment-stripped, whitespace-collapsed text (the code-identity normal form)."""
    return " ".join(strip_comments(text).split())


# ------------------------------------------------------------------ the import graph


def mod_of_path(rel):
    return rel[:-5].replace("/", ".")


def path_of_mod(m):
    return m.replace(".", "/") + ".lean"


def header_imports(text):
    """The imports of a module header (comments and blank lines skipped)."""
    src, i, res = text, 0, []
    n = len(src)
    while i < n:
        if src.startswith("/-", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if src.startswith("/-", j):
                    depth += 1; j += 2
                elif src.startswith("-/", j):
                    depth -= 1; j += 2
                else:
                    j += 1
            i = j
        elif src.startswith("--", i):
            j = src.find("\n", i); i = n if j < 0 else j
        elif src[i].isspace():
            i += 1
        elif src.startswith("import ", i):
            j = src.find("\n", i); j = n if j < 0 else j
            res += src[i:j].split()[1:]; i = j
        else:
            break
    return res


def graph(root, overlay=None):
    """module -> its `TCSlib` imports, over `root`/TCSlib and `root`/TCSlib.lean; files of the
    overlay directory (the landing tree) replace the root's."""
    g = {}
    for dp, _, fs in os.walk(os.path.join(root, "TCSlib")):
        for f in fs:
            if f.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, f), root)
                p = os.path.join(overlay, rel) if overlay and os.path.isfile(
                    os.path.join(overlay, rel)) else os.path.join(root, rel)
                g[mod_of_path(rel)] = [m for m in header_imports(rd(p)) if m.startswith("TCSlib")]
    g["TCSlib"] = [m for m in header_imports(rd(os.path.join(root, "TCSlib.lean")))
                   if m.startswith("TCSlib")]
    return g


def up(g, ms):
    seen, todo = set(), list(ms)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo += g.get(m, [])
    return seen


def rev(g):
    r = {m: [] for m in g}
    for m, ds in g.items():
        for d in ds:
            r.setdefault(d, []).append(m)
    return r


def down(g, ms):
    r = rev(g)
    seen, todo = set(), list(ms)
    while todo:
        m = todo.pop()
        if m in seen:
            continue
        seen.add(m)
        todo += r.get(m, [])
    return seen


def topo(g, ms):
    ms = set(ms)
    order, seen = [], set()

    def visit(m):
        if m in seen:
            return
        seen.add(m)
        for d in sorted(g.get(m, [])):
            visit(d)
        if m in ms:
            order.append(m)
    for m in sorted(ms):
        visit(m)
    return order


def git(*a):
    return subprocess.run(["git", "-C", REPO] + list(a), check=True, capture_output=True,
                          text=True).stdout


def tip():
    return git("rev-parse", "--verify", BRANCH + "^{commit}").strip()


# the base of the olean snapshot: #98's merge (MIG-1 stage S), whose replay output is oleans-lmig1s
# (the earlier runs used c9cc485b, the merged tip of #95-#97, with its catch-up replay oleans-ltip3)
SNAP_BASE = "eb750e63ff43"


def base_commit():
    """The commit the export was made from (run.sh: `git rev-parse` of the tip at the start)."""
    return rd(os.path.join(L, "work", "base-commit.txt")).strip()


def lean_diff(a, b):
    return git("diff", "--name-only", a, b, "--", "*.lean").split()
