import sys
draft, src = sys.argv[1], sys.argv[2]
d = open(draft).read().split("\n")
s = open(src).read().split("\n")
# the draft's lean block
i = d.index("```lean"); j = d.index("```", i + 1)
block = d[i + 1:j]
blank = block.index("")
u = block[:blank]; e = block[blank + 1:]
src_u = s[1715:1725]   # lines 1716..1725
src_e = s[1753:1760]   # lines 1754..1760
print("U2-U block == src 1716-1725:", u == src_u, len(u))
print("U2-E block == src 1754-1760:", e == src_e, len(e))
for a, b in zip(u, src_u):
    if a != b: print("DIFF U", repr(a), repr(b))
for a, b in zip(e, src_e):
    if a != b: print("DIFF E", repr(a), repr(b))
# region anchors
def L(n): return s[n - 1]
print("11:", L(11)); print("29-32:", [L(n)[:40] for n in range(29, 33)]); print("33:", repr(L(33)))
print("1687:", L(1687)); print("1688:", repr(L(1688))); print("1689:", L(1689)[:50])
print("1715 ends:", L(1715)[-6:]); print("1725:", L(1725)); print("1727:", L(1727)); print("1728:", repr(L(1728)))
print("1729:", L(1729)[:40]); print("1753 ends:", L(1753)[-6:]); print("1760:", L(1760)); print("total lines:", len(s) - (1 if s[-1] == "" else 0))
# docstring ranges 1689-1715 / 1729-1753 start with /-- and end with -/
print("1689 starts /--:", L(1689).startswith("/--"), "1729 starts /--:", L(1729).startswith("/--"))
