"""A small declaration parser for the Diagonal Part 1 checks (standard library only).

`parse(text)` returns the top-level declarations of a Lean file, in order, as dicts with
`kind`, `name` (fully qualified, from `namespace`/`end` tracking), `private`, `doc` (the
`/-- … -/` immediately before, or ''), `head` (from the declaration keyword up to, not
including, its top-level ` :=` or ` where`, or the whole declaration if it has neither),
`body` (the rest of the declaration text) and `line` (1-based). A declaration ends where the
next column-0 item begins (a declaration, a docstring, `namespace`, `end`, `section`, `open`,
`variable`, `set_option`, a `/-!` comment or `#`-command).
"""
import re

DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:private|protected|noncomputable|nonrec)\s+)*)"
                  r"(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque)\s+"
                  r"([^\s:({\[]+)")
STOP = re.compile(r"^(/--|/-!|namespace\b|end\b|section\b|noncomputable section\b|open\b|"
                  r"variable\b|set_option\b|#|@\[|attribute\b|(?:(?:private|protected|"
                  r"noncomputable|nonrec)\s+)*(theorem|lemma|def|abbrev|instance|structure|"
                  r"inductive|class|opaque)\b)")


def split_head(text):
    """Split a declaration at its first top-level ` :=` or ` where`."""
    depth = 0
    i = 0
    n = len(text)
    while i < n:
        ch = text[i]
        if ch in "([{⟨":
            depth += 1
        elif ch in ")]}⟩":
            depth -= 1
        elif depth == 0 and text.startswith(" :=", i):
            return text[:i], text[i:]
        elif depth == 0 and re.match(r"\swhere\b", text[i:i + 7]):
            return text[:i], text[i:]
        i += 1
    return text, ""


def parse(text):
    lines = text.split("\n")
    ns = []
    out = []
    i = 0
    pending_doc = None
    in_block_comment = False
    while i < len(lines):
        l = lines[i]
        if l.startswith("/--"):
            j = i
            while "-/" not in lines[j]:
                j += 1
            pending_doc = "\n".join(lines[i:j + 1])
            i = j + 1
            continue
        if l.startswith("/-") and not l.startswith("/--"):
            j = i
            while "-/" not in lines[j]:
                j += 1
            i = j + 1
            pending_doc = None
            continue
        m_ns = re.match(r"^namespace\s+(\S+)", l)
        if m_ns:
            ns.append(("ns", m_ns.group(1)))
            i += 1
            continue
        if re.match(r"^(noncomputable\s+)?section\b", l):
            ns.append(("sec", ""))
            i += 1
            continue
        if re.match(r"^end\b", l):
            if ns:
                ns.pop()
            i += 1
            continue
        m = DECL.match(l)
        if m:
            mods, kind, name = m.group(1), m.group(2), m.group(3)
            j = i + 1
            while j < len(lines) and not (lines[j] and not lines[j][0].isspace()
                                          and STOP.match(lines[j])):
                j += 1
            # trim trailing blank lines
            k = j
            while k > i and not lines[k - 1].strip():
                k -= 1
            decl = "\n".join(lines[i:k])
            prefix = ".".join(x[1] for x in ns if x[0] == "ns" and x[1])
            full = (prefix + "." + name) if prefix and not name.startswith("_root_.") \
                else name.replace("_root_.", "")
            head, body = split_head(decl)
            out.append({"kind": kind, "name": full, "private": "private" in mods,
                        "doc": pending_doc or "", "head": head, "body": body, "line": i + 1,
                        "text": decl})
            pending_doc = None
            i = j
            continue
        if l.strip():
            pending_doc = None if not l.startswith("@[") else pending_doc
        i += 1
    return out
