"""Relocation helpers: map base path:line to the tip, and find declarations at the tip (git objects only)."""
import re, subprocess, functools

REPO = '/home/user/tcslib'
TIP = '2be7eb209ae89c9dfe5ba7b63b115ae486ff9ffd'


def git(*a):
    return subprocess.run(['git', '-C', REPO, *a], capture_output=True, text=True).stdout


@functools.lru_cache(None)
def src(rev, path):
    r = subprocess.run(['git', '-C', REPO, 'show', f'{rev}:{path}'], capture_output=True, text=True)
    return r.stdout.splitlines() if r.returncode == 0 else None


@functools.lru_cache(None)
def hunks(base, path):
    d = git('diff', '-U0', base, TIP, '--', path)
    hs = []
    for m in re.finditer(r'^@@ -(\d+)(?:,(\d+))? \+(\d+)(?:,(\d+))? @@', d, re.M):
        a, b, c, e = int(m[1]), int(m[2] or 1), int(m[3]), int(m[4] or 1)
        hs.append((a, b, c, e))
    return hs


def mapline(base, path, L):
    """old line L -> new line, or None if the line itself changed."""
    delta = 0
    for a, b, c, e in hunks(base, path):
        if b == 0:  # pure insertion after old line a
            if L > a:
                delta += e
            continue
        if a <= L < a + b:
            return None
        if L >= a + b:
            delta += e - b
    return L + delta


DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|partial|unsafe|nonrec)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|opaque|axiom)\s+([^\s:({\[]+)')


def enclosing(rev, path, L):
    s = src(rev, path)
    if not s or L is None:
        return None
    for i in range(min(L, len(s)) - 1, -1, -1):
        m = DECL.match(s[i])
        if m:
            return (m[2], i + 1)
    return None


def find_decl(rev, path, name):
    """line of the declaration whose name ends with the last component(s) of `name`."""
    s = src(rev, path)
    if not s:
        return None
    parts = name.split('.')
    cands = []
    for i, line in enumerate(s):
        m = DECL.match(line)
        if not m:
            continue
        n = m[2]
        for k in range(len(parts), 0, -1):
            suf = '.'.join(parts[-k:])
            if n == suf or n.endswith('.' + suf):
                cands.append((k, i + 1))
                break
    if not cands:
        return None
    cands.sort(key=lambda t: -t[0])
    return cands[0][1]
