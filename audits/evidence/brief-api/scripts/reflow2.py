"""Rewrap docstrings (/-- and /-!) that mention a marker to 100 columns, paragraph by paragraph,
keeping inline code spans whole. Usage: python3 -I reflow2.py <file> <marker>"""
import sys, re, textwrap
p, marker = sys.argv[1], sys.argv[2]
s = open(p).read()
def fix(m):
    body = m.group(0); opener = body[:4]
    if marker not in body: return body
    inner = body[4:-2].rstrip()
    paras = re.split(r"\n\s*\n", inner.strip())
    out = []
    for i, para in enumerate(paras):
        words = " ".join(para.split())
        parts = words.split("`")
        words = "`".join(x.replace(" ", " ") if k % 2 else x for k, x in enumerate(parts))
        w = textwrap.fill(words, width=100, initial_indent=opener if i == 0 else "",
                          subsequent_indent="", break_long_words=False, break_on_hyphens=False)
        out.append(w.replace(" ", " "))
    res = "\n\n".join(out)
    last = res.split("\n")[-1]
    return res + (" -/" if len(last) + 3 <= 100 else "\n-/")
s2 = re.sub(r"/-[-!] .*?-/", fix, s, flags=re.S)
open(p, "w").write(s2); print("ok")
