"""Freeze of every touched existing file of the U2 unit (read-only; standard library only).

Usage: python3 -I freeze.py <base root> <landed root>

For each touched existing file: every base declaration is present in the landed file with the
same kind and name (or, for a listed promotion, under its new name), and its signature (its head
without the visibility, keyword and name) is byte-identical; visibility changes only for the
listed promotions. Reports changed bodies and docstrings, new declarations, header differences
(only added `import` lines are allowed), and admissions added (`sorry` occurrences in code may
only decrease). Exit 1 on any failure.
"""
import os
import re
import sys

sys.path.insert(0, os.path.dirname(__file__))
from decls import parse  # noqa: E402

TM = "TCSlib/Complexity/TuringMachine"
FILES = [f"{TM}/Build/StepBlockLoop.lean", f"{TM}/Codes2Tape.lean", f"{TM}/SelfUniversal.lean",
         "TCSlib/Complexity/TuringMachine.lean"]
PROMOTIONS = {"Turing.twoTape_serialize_eq": "Turing.Code2TM.serialize_eq_serializeK"}
SIG = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                 r"(?:theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+\S+")


def strip_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith("/-", i):
            depth, i = depth + 1, i + 2
        elif depth and src.startswith("-/", i):
            depth, i = depth - 1, i + 2
        elif depth:
            i += 1
        elif src.startswith("--", i):
            j = src.find("\n", i)
            i = n if j < 0 else j
        else:
            out.append(src[i])
            i += 1
    return "".join(out)


def header(src):
    return src[:src.index("/-!")] if "/-!" in src else src


def sig(d):
    return SIG.sub("", d["head"], count=1)


def main():
    base_root, land_root = sys.argv[1:3]
    fail = []
    for rel in FILES:
        b_src = open(os.path.join(base_root, rel), encoding="utf-8").read()
        l_src = open(os.path.join(land_root, rel), encoding="utf-8").read()
        base, land = parse(b_src), parse(l_src)
        lmap = {d["name"]: d for d in land}
        print(f"## {rel}")
        bh, lh = header(b_src).split("\n"), header(l_src).split("\n")
        added = [l for l in lh if l not in bh]
        removed = [l for l in bh if l not in lh]
        ok_header = not removed and all(l.startswith("import ") for l in added)
        print(f"header: removed lines {len(removed)}, added lines {added if added else 'none'}: "
              f"{'ok' if ok_header else '**NOT OK**'}")
        if not ok_header:
            fail.append(f"{rel}: header")
        print(f"received declarations: {len(base)}")
        print("| declaration | kind | visibility | signature | body | docstring |")
        print("|---|---|---|---|---|---|")
        for d in base:
            name = PROMOTIONS.get(d["name"], d["name"])
            e = lmap.get(name)
            if e is None or e["kind"] != d["kind"]:
                fail.append(f"{rel}: missing {d['name']}")
                print(f"| `{d['name']}` | {d['kind']} | | **MISSING** | | |")
                continue
            same = sig(e) == sig(d)
            if not same:
                fail.append(f"{rel}: signature changed: {d['name']}")
            vis_b = "private" if d["private"] else "public"
            vis_l = "private" if e["private"] else "public"
            if vis_b != vis_l and d["name"] not in PROMOTIONS:
                fail.append(f"{rel}: visibility changed: {d['name']}")
            vis = vis_b if vis_b == vis_l else f"{vis_b} → {vis_l}"
            label = f"`{d['name']}`" + (f" → `{name}`" if name != d["name"] else "")
            changed_any = e["body"] != d["body"] or e["doc"] != d["doc"] or name != d["name"]
            if changed_any or vis_b != vis_l:
                print(f"| {label} | {d['kind']} | {vis} | {'identical' if same else '**CHANGED**'}"
                      f" | {'unchanged' if e['body'] == d['body'] else 'changed'} | "
                      f"{'unchanged' if e['doc'] == d['doc'] else 'changed'} |")
        unchanged = sum(1 for d in base if (e := lmap.get(PROMOTIONS.get(d["name"], d["name"])))
                        and e["body"] == d["body"] and e["doc"] == d["doc"]
                        and PROMOTIONS.get(d["name"], d["name"]) == d["name"])
        print(f"(the other {unchanged} received declarations: signature, body and docstring "
              f"unchanged)")
        bnames = {PROMOTIONS.get(d["name"], d["name"]) for d in base}
        new = [d for d in land if d["name"] not in bnames]
        print(f"new declarations ({len(new)}): " + (", ".join(f"`{d['name']}`" for d in new)
                                                     if new else "none"))
        sb = len(re.findall(r"\bsorry\b", strip_comments(b_src)))
        sl = len(re.findall(r"\bsorry\b", strip_comments(l_src)))
        print(f"`sorry` in code: base {sb}, landed {sl}")
        new_sorry = sum(1 for d in new if re.search(r"\bsorry\b", strip_comments(d["body"])))
        old_sorry_kept = sl - new_sorry
        if old_sorry_kept > sb:
            fail.append(f"{rel}: a received proof became sorry")
        for d in base:
            e = lmap.get(PROMOTIONS.get(d["name"], d["name"]))
            if e and re.search(r"\bsorry\b", strip_comments(e["body"])) and not re.search(
                    r"\bsorry\b", strip_comments(d["body"])):
                fail.append(f"{rel}: proof of {d['name']} replaced by sorry")
        print()
    if fail:
        print("FREEZE: FAIL — " + "; ".join(fail))
        sys.exit(1)
    print("FREEZE: PASS — every received signature byte-identical in the 4 touched files; "
          "headers only gain imports; no received proof became `sorry`")


if __name__ == "__main__":
    main()
