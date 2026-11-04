"""Inspection table, step 1: extract every identifier passed to rw/simp/simpa/dsimp/unfold/show/
change (and their variants) in the fill's region of the owned file, and write a scratch copy of
the module that resolves each one (`#qy_resolve`) at the end of its namespace.

Usage: gen_inspect.py <owned.lean> <base-rev> <out-dir>
Writes <out-dir>/inspect-idents.tsv (identifier, tactic kinds, count, first line) and
<out-dir>/QyInspect.lean."""
import collections
import re
import subprocess
import sys

owned, base, outdir = sys.argv[1:4]
src = open(owned).read().split("\n")
# the fill's lines: those added against the base (git diff -U0 hunks)
diff = subprocess.run(["git", "diff", "-U0", base, "--", owned], capture_output=True, text=True,
                      check=True).stdout
mine = set()
for h in re.finditer(r"^@@ -\d+(?:,\d+)? \+(\d+)(?:,(\d+))? @@", diff, re.M):
    a, n = int(h.group(1)), int(h.group(2) or 1)
    mine.update(range(a, a + n))
text_lines = [(i + 1, l) for i, l in enumerate(src) if (i + 1) in mine]
# strip comments and docstrings (crude: drop text between /- and -/, and after --)
clean = []
depth = 0
for ln, l in text_lines:
    out = ""
    j = 0
    while j < len(l):
        if l.startswith("/-", j):
            depth += 1; j += 2; continue
        if depth and l.startswith("-/", j):
            depth -= 1; j += 2; continue
        if not depth and l.startswith("--", j):
            break
        if not depth:
            out += l[j]
        j += 1
    clean.append((ln, out))
joined = ""
starts = []  # (offset, line)
for ln, l in clean:
    starts.append((len(joined), ln))
    joined += l + "\n"


def line_of(off):
    lo = 0
    for o, ln in starts:
        if o <= off:
            lo = ln
        else:
            break
    return lo


IDENT = re.compile(r"[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][A-Za-z0-9_'\u2080-\u2089\u03b1-\u03c9\u0391-\u03a9!?]*"
                   r"(?:\.[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][A-Za-z0-9_'\u2080-\u2089\u03b1-\u03c9!?]*)*")
KW = {"at", "only", "with", "fun", "by", "from", "if", "then", "else", "let", "have", "show",
      "in", "do", "match", "Type", "Prop", "Sort", "this", "true", "false", "using", "config",
      "decide", "sorry", "rfl", "_"}
occ = collections.defaultdict(lambda: [set(), 0, None])
BR = re.compile(r"\b(rw|rwa|rewrite|erw|simp_rw|nth_rw|nth_rewrite|simp|simpa|dsimp|simp_all|"
                r"norm_num|field_simp|push_cast|simp_arith)\b(\?)?(\s+only)?(\s*\(config[^)]*\))?\s*\[")
for m in BR.finditer(joined):
    k = m.group(1) + (" only" if m.group(3) else "")
    j = m.end()
    d = 1
    while d and j < len(joined):
        if joined[j] == "[":
            d += 1
        elif joined[j] == "]":
            d -= 1
        j += 1
    for t in IDENT.findall(joined[m.end():j - 1]):
        if t in KW:
            continue
        o = occ[t]; o[0].add(k); o[1] += 1; o[2] = o[2] or line_of(m.start())
for m in re.finditer(r"\b(unfold|delta)\b([^\n]*)", joined):
    arg = re.split(r"\bat\b", m.group(2))[0]
    for t in IDENT.findall(arg):
        if t in KW:
            continue
        o = occ[t]; o[0].add(m.group(1)); o[1] += 1; o[2] = o[2] or line_of(m.start())
lines = joined.split("\n")
for idx, l in enumerate(lines):
    for m in re.finditer(r"\b(show|change)\b", l):
        seg = l[m.end():]
        ind = len(l) - len(l.lstrip())
        k2 = idx + 1
        while k2 < len(lines) and lines[k2].strip() and (len(lines[k2]) - len(lines[k2].lstrip())) > ind + 2:
            seg += " " + lines[k2]
            k2 += 1
        seg = re.split(r"\bfrom\b|:= by|\bby\b", seg)[0]
        for t in IDENT.findall(seg):
            if t in KW:
                continue
            o = occ[t]; o[0].add(m.group(1)); o[1] += 1
            o[2] = o[2] or line_of(sum(len(x) + 1 for x in lines[:idx]))
# normalize: drop proof-term suffixes; read `κ.foo` (dot notation on the kit) as `QyKit.foo`
norm = collections.defaultdict(lambda: [set(), 0, None])
for t, (k, c, ln) in occ.items():
    u = re.sub(r"(\.(mp|mpr|symm|le|1|2|trans|elim|ne|ne'|out))+$", "", t)
    if u.startswith("κ."):
        u = "QyKit." + u[2:]
    o = norm[u]; o[0] |= k; o[1] += c; o[2] = o[2] or ln
occ = norm
names = sorted(occ)
with open(f"{outdir}/inspect-idents.tsv", "w") as f:
    for n in names:
        k, c, ln = occ[n]
        f.write(f"{n}\t{','.join(sorted(k))}\t{c}\t{ln}\n")
tail = ["", "open Lean Elab Command Term in",
        "/-- Resolve each identifier as the fill's code sees it here; print its kind and module. -/",
        "elab \"#qy_resolve \" xs:ident* : command => do",
        "  let env ← getEnv",
        "  let mut out : Array String := #[]",
        "  for x in xs do",
        "    let r ← try (some <$> liftTermElabM (realizeGlobalConstNoOverload x)) catch _ => pure none",
        "    match r with",
        "    | none => out := out.push s!\"{x.getId}\\t-\\t(unresolved: a local, a field or a binder)\\t-\"",
        "    | some c =>",
        "      let some ci := env.find? c | continue",
        "      let kind := match ci with",
        "        | .thmInfo _ => \"theorem\" | .defnInfo _ => \"def\" | .inductInfo _ => \"inductive\"",
        "        | .ctorInfo _ => \"ctor\" | .recInfo _ => \"rec\" | .axiomInfo _ => \"axiom\"",
        "        | .opaqueInfo _ => \"opaque\" | .quotInfo _ => \"quot\"",
        "      let kind := if (env.getProjectionFnInfo? c).isSome then kind ++ \" (projection)\" else kind",
        "      let m := match env.getModuleIdxFor? c with",
        "        | none => \"(this file)\" | some i => (env.header.moduleNames[i.toNat]!).toString",
        "      out := out.push s!\"{x.getId}\\t{c}\\t{kind}\\t{m}\"",
        "  logInfo m!\"QYRESOLVE {out.size}\\n{\"\\n\".intercalate out.toList}\"",
        ""]
chunks = [names[i:i + 40] for i in range(0, len(names), 40)]
for ch in chunks:
    tail.append("#qy_resolve " + " ".join(ch))
assert src[-2] == "end Turing.NTimeDiag"
open(f"{outdir}/QyInspect.lean", "w").write("\n".join(src[:-2] + tail + [""] + src[-2:]))
print(f"{len(names)} identifiers from {len(text_lines)} added lines")
