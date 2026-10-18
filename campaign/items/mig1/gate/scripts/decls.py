import re, sys, json
# List declarations of a Lean file: (start line, end line, kind, private, name)
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class)'
pat = re.compile(r'^(?:@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*' + KW + r'\s+([^\s:({\[]+)?')
def scan(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    # strip comment blocks: track nesting for /- -/
    depth = 0
    starts = []
    code_flags = []
    for i, l in enumerate(lines):
        s = l
        out = ''
        j = 0
        while j < len(s):
            if depth > 0:
                if s.startswith('/-', j): depth += 1; j += 2; continue
                if s.startswith('-/', j): depth -= 1; j += 2; continue
                j += 1; continue
            if s.startswith('/-', j): depth += 1; j += 2; continue
            if s.startswith('--', j): break
            out += s[j]; j += 1
        code_flags.append(out)
        m = pat.match(out)
        if m and not out.startswith(' '):
            pre = out[:m.start(2)]
            starts.append((i + 1, m.group(2), 'private' in pre, m.group(3) or '', out.strip()))
    res = []
    n = len(lines)
    # end line: line before next decl start / next top-level docstring / namespace/end/section
    toplevel = set()
    for i, l in enumerate(lines):
        if re.match(r'^(/--|/-!|namespace |end |section|variable|open |set_option|@\[|private |theorem|lemma|def |abbrev|structure|inductive|instance|noncomputable|protected|attribute)', l):
            toplevel.add(i + 1)
    tl = sorted(toplevel)
    import bisect
    for (ln, kind, priv, name, text) in starts:
        k = bisect.bisect_right(tl, ln)
        end = (tl[k] - 1) if k < len(tl) else n
        # trim trailing blank lines
        while end > ln and lines[end - 1].strip() == '':
            end -= 1
        res.append(dict(line=ln, end=end, kind=kind, private=priv, name=name, head=text[:160]))
    return res, lines
if __name__ == '__main__':
    r, _ = scan(sys.argv[1])
    json.dump(r, open(sys.argv[2], 'w'), indent=0)
    print(len(r))
