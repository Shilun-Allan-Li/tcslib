"""Helpers: delete a top-level declaration (with its docstring) by name; regex rename."""
import re
TOP = re.compile(r'^(/--|/-!|private |theorem |lemma |def |noncomputable |@\[|section|end |namespace |open |variable |instance |abbrev |protected )')
def delete_decl(s, name):
    L = s.split('\n')
    pat = re.compile(r'^(private |protected )?(noncomputable )?(theorem|lemma|def|abbrev) ' + re.escape(name) + r'(\s|$)')
    idx = [i for i, l in enumerate(L) if pat.match(l)]
    assert len(idx) == 1, (name, idx)
    i = idx[0]
    a = i
    if a > 0 and (L[a-1].rstrip().endswith('-/')):
        a -= 1
        while not L[a].startswith('/--'):
            a -= 1
    b = i + 1
    while b < len(L) and not TOP.match(L[b]):
        b += 1
    # keep exactly the separation: drop trailing blank lines of the removed block
    del L[a:b]
    return '\n'.join(L)
def rename(s, old, new):
    n = len(re.findall(r'(?<![\w.])' + re.escape(old) + r'(?![\w])', s))
    s = re.sub(r'(?<![\w.])' + re.escape(old) + r'(?![\w])', new, s)
    return s, n
