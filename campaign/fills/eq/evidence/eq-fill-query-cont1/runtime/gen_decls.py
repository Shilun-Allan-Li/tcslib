"""Every new declaration with its role: one row per declaration of the dev modules (landed as
`private`), with its kind and its docstring's first sentence. Usage: gen_decls.py <mods...>"""
import re
import sys
DECL = re.compile(r"^(theorem|lemma|def|abbrev|inductive|structure|instance)\s+([^\s:({\[]+)")
for m in sys.argv[1:]:
    lines = open(f"/home/user/tcslib/evidence/dev/{m}.lean").read().split("\n")
    print(f"\n**{m}**\n")
    print("| declaration | kind | role (docstring's first sentence) |")
    print("|---|---|---|")
    for i, l in enumerate(lines):
        d = DECL.match(l)
        if not d:
            continue
        j = i - 1
        while j >= 0 and lines[j].startswith("@["):
            j -= 1
        k = j
        while k >= 0 and "/--" not in lines[k]:
            k -= 1
        doc = " ".join(x.strip() for x in lines[k:j + 1]).replace("/--", "").replace("-/", "").strip()
        s = re.split(r"(?<=\.)\s", doc, maxsplit=1)[0]
        s = s.replace("|", "\\|")
        if len(s) > 200:
            s = s[:197] + "..."
        print(f"| `{d.group(2)}` | {d.group(1)} | {s} |")
