import re, sys
KW = r'(theorem|lemma|def|abbrev|instance|structure|inductive|class)'
DECL = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW + r'\s+([^\s(:{\[]+)')
# v3 (gate 69 round 2 and gate 71, minor 1): anonymous instances are declarations too; they
# were skipped and their text absorbed into the previous chunk. Each is keyed by its statement.
ANON = re.compile(r'^(@\[[^\]]*\]\s*)*((private|protected|noncomputable|nonrec|partial|unsafe)\s+)*instance(?=\s*[(:{\[]|\s*$)')
STOP = re.compile(r'^(end\b|namespace\b|section\b|/-!|open\b|variable\b|set_option\b|#|attribute\b|universe\b)')
# v4 (gate 78, minor 2): declarations are keyed by their namespace-qualified name, so that two
# declarations with one short name in different namespaces (`Segment.trans`, `SafeSegment.trans`) are not
# collapsed; a name that is still not unique gets `#k` (k-th in source order).
SCOPE = re.compile(r'^(?:(namespace)\s+(\S+)|(?:noncomputable\s+)?(section)\b\s*(\S*)|(mutual)\b|(end)\b\s*(\S*))')
def chunks(text):
    lines = text.split('\n'); out = []; pend = None; cur = None; depth = 0; stack = []
    def ns():
        return '.'.join(n for k, n in stack if k == 'namespace')
    def qualify(name):
        if name.startswith('_root_.'): return name[len('_root_.'):]
        return f'{ns()}.{name}' if ns() else name
    def close(i):
        nonlocal cur
        if cur:
            text = '\n'.join(lines[cur[2]:i]).rstrip()
            name = cur[0]
            if name is None:
                name = 'instance⟨' + stmt(text) + '⟩'
                while any(n == name for n, _, _ in out): name += "'"
            else:
                base = name; k = 1
                while any(n == name for n, _, _ in out): k += 1; name = f'{base}#{k}'
            out.append((name, cur[1], text))
        cur = None
    for i, l in enumerate(lines):
        # v2 (B5b gate, minor 5): a line that starts inside a block comment or docstring is never
        # a declaration or a stop line (a docstring line "instance of ..." was counted as one).
        start_depth, j = depth, 0
        while j < len(l):
            if l.startswith('/-', j): depth += 1; j += 2; continue
            if l.startswith('-/', j) and depth > 0: depth -= 1; j += 2; continue
            if depth == 0 and l.startswith('--', j): break
            j += 1
        if start_depth > 0: continue
        if l.startswith('/--'):
            close(i); pend = i; continue
        m = DECL.match(l)
        if m:
            if pend is None: close(i)
            start = pend if pend is not None else i; pend = None
            cur = (qualify(m.group(5)), l.lstrip().startswith('private') or ' private ' in l.split(m.group(4))[0], start)
            continue
        m = ANON.match(l)
        if m:
            if pend is None: close(i)
            start = pend if pend is not None else i; pend = None
            cur = (None, l.lstrip().startswith('private'), start)
            continue
        if STOP.match(l):
            close(i); pend = None
            sm = SCOPE.match(l)
            if sm:
                if sm.group(1): stack += [('namespace', c) for c in sm.group(2).split('.')]
                elif sm.group(3): stack.append(('section', sm.group(4)))
                elif sm.group(5): stack.append(('mutual', ''))
                else:
                    for c in reversed(sm.group(7).split('.')):
                        if stack and stack[-1][1] == c: stack.pop()
                        elif stack and c == '': stack.pop()
    close(len(lines))
    return out
def stmt(t):
    body = t.split('-/', 1)[1] if t.startswith('/--') else t
    s = re.split(r':=', body, maxsplit=1)[0]
    return ' '.join(s.split())
