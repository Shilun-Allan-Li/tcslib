"""Produce an inert proof-only proposal; never write the actual Loop source."""
from pathlib import Path
import difflib
import hashlib
import json
import re

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[4]
ns = {}
tool = (ROOT / 'devtools/seyoon/declfreeze.py').read_text()
exec(compile(tool.split('a = chunks(')[0], 'trusted-declfreeze-helper', 'exec'), ns)
chunks = ns['chunks']


def assignment(s):
    stack = []
    comment = 0
    string = False
    i = 0
    pairs = {')': '(', ']': '[', '}': '{', '⟩': '⟨'}
    while i < len(s):
        if comment:
            if s.startswith('/-', i):
                comment += 1
                i += 2
                continue
            if s.startswith('-/', i):
                comment -= 1
                i += 2
                continue
            i += 1
            continue
        if string:
            if s[i] == '\\':
                i += 2
                continue
            if s[i] == '"':
                string = False
            i += 1
            continue
        if s.startswith('/-', i):
            comment = 1
            i += 2
            continue
        if s.startswith('--', i):
            end = s.find('\n', i)
            i = len(s) if end < 0 else end + 1
            continue
        c = s[i]
        if c == '"':
            string = True
        elif c in '([{⟨':
            stack.append(c)
        elif c in pairs:
            assert stack and stack.pop() == pairs[c], (i, c)
        elif not stack and s.startswith(':=', i):
            return i
        i += 1
    return None


def split(s):
    i = assignment(s)
    return (s, None) if i is None else (s[:i], s[i + 2:])


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()


