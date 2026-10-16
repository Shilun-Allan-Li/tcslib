"""Rewrap the docstrings that mention a marker to 100 columns, paragraph by paragraph.
Usage: python3 -I reflow.py <file> <marker>"""
import sys, re, textwrap
p, marker = sys.argv[1], sys.argv[2]
s = open(p).read()
def fix(m):
    body = m.group(0)
    if marker not in body: return body
    inner = body[len("/-- "):-len(" -/")] if body.endswith(" -/") else body[len("/-- "):-len("-/")]
    paras = re.split(r"\n\s*\n", inner.strip())
    out = []
    for i, para in enumerate(paras):
        words = " ".join(para.split())
        # keep inline code spans unbreakable
        parts = words.split("`")
        words = "`".join(x.replace(" ", "\u00a0") if k % 2 else x for k, x in enumerate(parts))
        first = "/-- " if i == 0 else ""
        w = textwrap.fill(words, width=100, initial_indent=first, subsequent_indent="",
                          break_long_words=False, break_on_hyphens=False)
        out.append(w.replace("\u00a0", " "))
    res = "\n\n".join(out)
    last = res.split("\n")[-1]
    return res + (" -/" if len(last) + 3 <= 100 else "\n-/")
s2 = re.sub(r"/-- .*?-/", fix, s, flags=re.S)
open(p, "w").write(s2)
print("ok")
