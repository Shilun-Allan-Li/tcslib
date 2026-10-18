"""Shared helpers of the cut checks (standard library only): the import header of a Lean file,
and `#print axioms` lines for its public declarations."""
import os
import sys

sys.path.insert(0, os.path.dirname(__file__))
from decls import parse  # noqa: E402


def split_header(src):
    """(imports, body): the header's `import` modules and the text after the last of them."""
    k, n, imps, end = 0, len(src), [], 0
    while k < n:
        if src[k].isspace():
            k += 1
        elif src.startswith("/-", k):
            depth, k = 1, k + 2
            while k < n and depth:
                if src.startswith("/-", k):
                    depth, k = depth + 1, k + 2
                elif src.startswith("-/", k):
                    depth, k = depth - 1, k + 2
                else:
                    k += 1
        elif src.startswith("--", k):
            e = src.find("\n", k)
            k = n if e < 0 else e
        elif src.startswith("import ", k):
            e = src.find("\n", k)
            e = n if e < 0 else e
            imps.extend(src[k + 7:e].split("--")[0].split())
            k = end = e
        else:
            break
    return imps, src[end:]


def prints(src):
    names = [d["name"] for d in parse(src) if not d["private"]
             and d["kind"] in ("theorem", "lemma", "def", "abbrev", "structure", "instance")]
    return "".join(f"\n#print axioms {n}" for n in names) + "\n", len(names)
