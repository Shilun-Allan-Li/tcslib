"""Statement correspondence (read-only; standard library only).

Usage: python3 -I sigdiff.py <old> <new> [<old>=<new> ...]

For every declaration of <old>, find the declaration of <new> with the same full name (after
the renames old=new, given as full names). Compare their *statements*: the comment-stripped
text from the keyword up to the first `:=` (or `where`, for structure-like definitions) outside
brackets, whitespace collapsed. Report identical, changed (with both texts) and missing;
declarations of <new> with no counterpart are listed as added. Section `variable` lines are
reported alongside, since they bind implicit arguments of the statements.
"""
import re
import sys

KW = r"(?:theorem|lemma|def|structure|abbrev|inductive|instance)"
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:noncomputable\s+)?(private\s+)?(?:noncomputable\s+)?"
                  + KW + r"\s+([A-Za-z0-9_.'«»₀-₉]+)", re.M)


def strip(src):
    out, i, depth = [], 0, 0
    while i < len(src):
        if src.startswith("/-", i):
            depth += 1
            i += 2
            continue
        if src.startswith("-/", i) and depth > 0:
            depth -= 1
            i += 2
            continue
        if depth == 0:
            out.append(src[i])
        i += 1
    return "\n".join(l.split("--")[0].rstrip() for l in "".join(out).splitlines())


def statement(text):
    depth = 0
    lets = 0
    i = 0
    while i < len(text):
        ch = text[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and re.match(r"\blet\b", text[i:]) and (i == 0 or not
                                                                (text[i - 1].isalnum() or text[i - 1] in "_.'")):
            lets += 1
        elif depth == 0 and text.startswith(":=", i) and lets > 0:
            lets -= 1
        elif depth == 0 and text.startswith(":=", i):
            return text[:i]
        elif depth == 0 and re.match(r"\swhere\b", text[i:]):
            return text[:i]
        i += 1
    return text


def decls(path):
    src = strip(open(path, encoding="utf-8").read())
    lines = src.split("\n")
    ns, res = [], {}
    scopes = [[]]  # variable lines per open section/namespace
    starts = []
    for idx, line in enumerate(lines):
        s = line.strip()
        m = re.match(r"namespace\s+(\S+)", s)
        if m:
            ns.append(m.group(1))
            scopes.append([])
        if re.match(r"section\b", s):
            scopes.append([])
        m2 = re.match(r"end\b\s*(\S*)", s)
        if m2:
            if m2.group(1) and ns and ns[-1] == m2.group(1):
                ns.pop()
            if len(scopes) > 1:
                scopes.pop()
        if s.startswith("variable"):
            scopes[-1].append(" ".join(s.split()))
        m3 = DECL.match(s)
        if m3:
            n = m3.group(2)
            n = n[len("_root_."):] if n.startswith("_root_.") else ".".join(ns + [n])
            starts.append((idx, n, [v for sc in scopes for v in sc]))
    for k, (idx, n, v) in enumerate(starts):
        end = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        body = "\n".join(lines[idx:end])
        res[n] = (" ".join(statement(body).split()), v)
    return res


def main():
    old, new = decls(sys.argv[1]), decls(sys.argv[2])
    ren = dict(a.split("=", 1) for a in sys.argv[3:])
    same = changed = missing = 0
    for n, (t, v) in old.items():
        n2 = ren.get(n, n)
        if n2 not in new:
            print(f"MISSING  {n}")
            missing += 1
            continue
        t2, v2 = new[n2]
        if t == t2:
            same += 1
        else:
            changed += 1
            print(f"CHANGED  {n}" + (f" -> {n2}" if n2 != n else ""))
            print(f"   old: {t}")
            print(f"   new: {t2}")
        if v != v2:
            print(f"   (variables differ) old: {v} | new: {v2}")
    used = {ren.get(n, n) for n in old}
    added = [n for n in new if n not in used]
    print(f"identical {same}, changed {changed}, missing {missing}; added: {len(added)}"
          + (": " + ", ".join(added) if added else ""))


if __name__ == "__main__":
    main()
