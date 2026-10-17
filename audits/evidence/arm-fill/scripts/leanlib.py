"""Shared helpers for the ARM-extensions fill-gate evidence scripts (read-only analysis).

strip(): nesting-aware removal of block comments (docstrings included) and line comments,
preserving line structure (each removed character other than a newline becomes nothing,
newlines inside comments are kept) so that line numbers survive.
decls(): declarations of a comment-stripped source, with kind, name, visibility, line.
"""
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
        # string literals: keep as-is (rare in this library); no special handling
        out.append(src[i]); i += 1
    return ''.join(out)

KINDS = r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)*((?:(?:private|protected|noncomputable|nonrec|partial|'
                  r'unsafe|scoped|local)\s+)*)' + KINDS + r'\b\s*([^\s(:{\[]*)')

def decls(stripped):
    res = []
    for ln, line in enumerate(stripped.split('\n'), 1):
        m = DECL.match(line)
        if m:
            mods = m.group(1).split()
            kind = m.group(2)
            if kind == 'class' and m.group(3) == 'inductive':
                kind = 'class inductive'
            res.append(dict(line=ln, kind=kind, name=m.group(3), private='private' in mods,
                            mods=mods))
    return res

def imports(src):
    return [m.group(1) for m in re.finditer(r'^import\s+(\S+)', src, re.M)]
