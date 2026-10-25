"""Parse the report's "## Files" section into paths and compare with the delivered file list.
Usage: filelist.py <report.md> <delivered-files.txt>"""
import re, sys
rep, deliv = sys.argv[1], sys.argv[2]
t = open(rep, encoding="utf-8").read()
sec = t[t.index("## Files"):]
items = re.split(r"\n- ", sec)[1:]
listed = set()
for it in items:
    it = " ".join(it.split())
    m = re.match(r"`([^`]+/)` \((\d+)\): (.*)", it)
    assert m, it[:80]
    d, n, rest = m.group(1), int(m.group(2)), m.group(3)
    names = re.findall(r"`([^`]+)`", rest)
    assert len(names) == n, (d, n, len(names))
    listed |= {d + x for x in names}
got = {l.strip() for l in open(deliv) if l.strip()}
print("listed", len(listed), "delivered", len(got))
print("listed not delivered:", sorted(listed - got))
print("delivered not listed:", sorted(got - listed))
