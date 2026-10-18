"""Split a Lean source into top-level items (standard library only).

An item is a declaration with its preceding doc comment, or a structural line
(namespace/end/section/variable/open/set_option/import), or a module/section doc
comment (`/-! ... -/`), or a run of blank lines. Declarations are named by their
declared identifier (with `_root_.` and the enclosing namespaces resolved).
"""
import re

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec)\s+)*'
                  r'(theorem|lemma|def|structure|abbrev|inductive|instance|class)\s+(\S+)')
START = re.compile(r'^(/--|/-!|namespace\b|end\b|section\b|variable\b|open\b|set_option\b|'
                   r'import\b|@\[|private\b|protected\b|noncomputable\b|theorem\b|lemma\b|'
                   r'def\b|structure\b|abbrev\b|inductive\b|instance\b|class\b|example\b|#|/-\s|--)')


def items(text):
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines = lines[:-1]
    out = []  # (kind, name, start, end) with 0-based [start, end)
    i, n = 0, len(lines)
    stack = []
    while i < n:
        l = lines[i]
        if l.strip() == '':
            j = i
            while j < n and lines[j].strip() == '':
                j += 1
            out.append(('blank', None, i, j))
            i = j
            continue
        if l.startswith('/-!') or (l.startswith('/-') and not l.startswith('/--')):
            j = i
            while '-/' not in lines[j][(3 if j == i else 0):] if j == i else '-/' not in lines[j]:
                j += 1
            out.append(('moddoc', None, i, j + 1))
            i = j + 1
            continue
        if l.startswith('/--'):
            # doc comment, then the declaration it documents
            j = i
            while '-/' not in (lines[j][3:] if j == i else lines[j]):
                j += 1
            k = j + 1
            while k < n and (lines[k].startswith('--') or (lines[k].startswith('/-')
                                                          and not lines[k].startswith('/--'))):
                if lines[k].startswith('--'):
                    k += 1
                    continue
                while '-/' not in lines[k]:
                    k += 1
                k += 1
            if k < n and lines[k].startswith('example'):
                e = decl_end(lines, k)
                out.append(('example', None, i, e))
                i = e
                continue
            m = DECL.match(lines[k]) if k < n else None
            assert m, f'doc comment at line {i + 1} not followed by a declaration'
            e = decl_end(lines, k)
            out.append(('decl', resolve(stack, m.group(2)), i, e))
            i = e
            continue
        m = DECL.match(l)
        if m:
            e = decl_end(lines, i)
            out.append(('decl', resolve(stack, m.group(2)), i, e))
            i = e
            continue
        mm = re.match(r'^namespace (\S+)', l)
        if mm:
            stack.append(('ns', mm.group(1)))
        elif re.match(r'^(noncomputable\s+)?section\b', l):
            stack.append(('sec', ''))
        elif re.match(r'^end\b', l):
            stack.pop()
        out.append(('line', l.strip(), i, i + 1))
        i += 1
    return lines, out


def decl_end(lines, k):
    e = k + 1
    while e < len(lines) and not (lines[e] and not lines[e][0].isspace()
                                  and START.match(lines[e])):
        e += 1
    while e > k + 1 and lines[e - 1].strip() == '':
        e -= 1
    return e


def resolve(stack, name):
    if name.startswith('_root_.'):
        return name[len('_root_.'):]
    ns = '.'.join(n for k, n in stack if k == 'ns')
    return f'{ns}.{name}' if ns else name


def decls(text):
    lines, its = items(text)
    return {nm: '\n'.join(lines[s:e]) for k, nm, s, e in its if k == 'decl'}, lines, its


if __name__ == '__main__':
    import sys
    lines, its = items(open(sys.argv[1], encoding='utf-8').read())
    for k, nm, s, e in its:
        if k != 'blank':
            print(f'{s + 1:5d}-{e:5d} {k:7s} {nm if nm else ""}')
