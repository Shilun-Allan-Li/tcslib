"""Shared primitives, copied verbatim in behaviour from round 1's ledger.py/leanlib.py:
strip_keep_lines (nesting-aware comment removal keeping newlines), the copy screen's
declaration regex DECL, and its body() extraction."""
import re
def strip_keep_lines(src):
    out = []; i = 0; depth = 0; n = len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth:
            if src[i] == '\n': out.append('\n')
            i += 1; continue
        if src.startswith('--', i):
            j = src.find('\n', i)
            if j < 0: break
            i = j; continue
        out.append(src[i]); i += 1
    return ''.join(out)
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)?((?:(?:noncomputable|private|protected)\s+)*)"
                  r"(def|theorem|lemma|abbrev|instance|structure|inductive)\s+(\S+)", re.M)
def body(b):
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif b.startswith(':=', i) and d == 0: return b[i + 2:]
    d = 0
    for i, ch in enumerate(b):
        if ch in '([{⟨': d += 1
        elif ch in ')]}⟩': d -= 1
        elif d == 0 and (ch == '|' or re.match(r'\bwhere\b', b[i:i + 6])): return b[i:]
    return ''
