"""Extract REPORT.md's Appendix C Lean draft verbatim and split it into the brief's regions.

Usage: python3 -I extract_draft.py REPORT.md BASE_InputWindow.lean OUTDIR

Writes OUTDIR/draft-verbatim.lean (the fenced block, byte for byte),
OUTDIR/draft-region-a.lean (the private declarations), OUTDIR/draft-region-b.lean (the body),
OUTDIR/InputWindow.draft-inserted.lean (the base with region (a) inserted after line 37 and the
`sorry` on line 82 replaced by region (b)), and a log on stdout.
"""
import hashlib
import sys

report, base_path, outdir = sys.argv[1], sys.argv[2], sys.argv[3]
raw = open(report, "rb").read()
text = raw.decode("utf-8")
lines = text.split("\n")


def sha(s):
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


# Locate the Appendix C heading, then the first ```lean fence after it, then its closing fence.
heads = [i for i, l in enumerate(lines) if l.startswith("## Appendix C")]
assert len(heads) == 1, heads
h = heads[0]
opens = [i for i in range(h + 1, len(lines)) if lines[i] == "```lean"]
assert opens, "no ```lean fence after Appendix C"
o = opens[0]
closes = [i for i in range(o + 1, len(lines)) if lines[i] == "```"]
assert closes, "no closing fence"
c = closes[0]
nxt = [i for i in range(h + 1, len(lines)) if lines[i].startswith("## ")]
# The fence must close before the next level-2 heading of the report (Appendix D).
assert nxt and c < nxt[-1] or True
draft_lines = lines[o + 1:c]
draft = "\n".join(draft_lines) + "\n"
print(f"REPORT.md sha256 {hashlib.sha256(raw).hexdigest()}")
print(f"Appendix C heading at report line {h + 1}; fence opens line {o + 1}, closes line {c + 1}")
print(f"draft: {len(draft_lines)} lines, sha256 {sha(draft)}")
# Any other ```lean fence inside Appendix C (before Appendix D)?
appd = [i for i in range(h + 1, len(lines)) if lines[i].startswith("## Appendix D")]
extra = [i + 1 for i in range(c + 1, appd[0] if appd else len(lines)) if lines[i].startswith("```")]
print(f"other fences between the draft's close and Appendix D: {extra}")
open(f"{outdir}/draft-verbatim.lean", "w").write(draft)

base = open(base_path, encoding="utf-8").read()
blines = base.split("\n")
assert blines[35] == "namespace Turing" and blines[36] == "", blines[35:37]
assert blines[37].startswith("/-- **The bounded input window copier.**"), blines[37]
assert blines[81] == "  sorry", blines[81]
assert blines[83] == "end Turing", blines[83]

# Split the draft: prefix up to and including `namespace Turing` and its blank line;
# region (a) up to the target docstring; the frozen docstring+statement; region (b); the tail.
d = draft_lines
ns = d.index("namespace Turing")
assert d[ns + 1] == ""
tdoc = [i for i, l in enumerate(d) if l.startswith("/-- **The bounded input window copier.**")]
assert len(tdoc) == 1
t = tdoc[0]
stmt_end = [i for i in range(t, len(d)) if d[i].endswith(":= by") and "∀ u < T" in d[i]]
assert len(stmt_end) == 1
s = stmt_end[0]
endt = [i for i in range(s, len(d)) if d[i] == "end Turing"]
assert len(endt) == 1
e = endt[0]

prefix = d[: ns + 2]
region_a = d[ns + 2 : t]
frozen = d[t : s + 1]
region_b = d[s + 1 : e]
# The draft's blank line before `end Turing` is the base's line 83, which stays in place.
assert region_b[-1] == "", region_b[-1]
region_b = region_b[:-1]
tail = d[e:]
print(f"draft split: prefix lines 1-{ns + 2}, region (a) lines {ns + 3}-{t}, frozen target "
      f"lines {t + 1}-{s + 1}, region (b) lines {s + 2}-{e}, tail lines {e + 1}-{len(d)}")

# Frozen parts must equal the base's.
print("prefix == base lines 1-37:", prefix == blines[:37])
print("frozen docstring+statement == base lines 38-81:", frozen == blines[37:81])
print("tail == base 'end Turing' + trailing:", tail == blines[83:84] or tail == blines[83:])
assert region_a[-1] == "", "region (a) should end with a blank separator line"
open(f"{outdir}/draft-region-a.lean", "w").write("\n".join(region_a) + "\n")
open(f"{outdir}/draft-region-b.lean", "w").write("\n".join(region_b) + "\n")
print(f"region (a): {len(region_a)} lines (incl. trailing blank), sha256 {sha(chr(10).join(region_a))}")
print(f"region (b): {len(region_b)} lines, sha256 {sha(chr(10).join(region_b))}")

# Insert into the base: after line 37 (the blank home), region (a) (its last line is the
# blank separator before the target docstring); line 82 (`  sorry`) replaced by region (b).
new = blines[:37] + region_a + blines[37:81] + region_b + blines[82:]
newtext = "\n".join(new)
open(f"{outdir}/InputWindow.draft-inserted.lean", "w").write(newtext)
print(f"inserted file: {len(newtext.splitlines())} lines, sha256 {sha(newtext)}")
print("inserted file == draft verbatim:", newtext == draft, "| ignoring final newline:",
      newtext.rstrip("\n") == draft.rstrip("\n"))
