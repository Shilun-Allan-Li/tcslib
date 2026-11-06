"""decls.py <root> <base-rev> <file>...: public declarations (full name -> (kind, line, normalized
statement)) at <base-rev> and in the working tree; prints added / removed / changed as TSV."""
import sys, re, subprocess
root, base = sys.argv[1], sys.argv[2]
files = sys.argv[3:]
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class)'
def strip(src):
    src = re.sub(r'/-.*?-/', lambda m: '\n' * m.group(0).count('\n'), src, flags=re.S)
    return re.sub(r'--[^\n]*', '', src)
def decls(src):
    lines = strip(src).split('\n')
    out, ns, i = {}, [], 0
    while i < len(lines):
        l = lines[i]
        m = re.match(r'^namespace\s+(\S+)', l)
        if m: ns.append(m.group(1)); i += 1; continue
        m = re.match(r'^end\s+(\S+)\s*$', l)
        if m and ns and ns[-1] == m.group(1): ns.pop(); i += 1; continue
        m = re.match(r'^(@\[[^\]]*\]\s*)?((?:private|protected|noncomputable|nonrec)\s+)*' + KW +
                     r'\s+([^\s(:{\[]+)', l)
        if m and not re.search(r'\bprivate\b', l.split(m.group(3))[0]):
            name = m.group(4)
            full = name[len('_root_.'):] if name.startswith('_root_.') else '.'.join(ns + [name])
            def cut(t):
                d = 0
                for k, ch in enumerate(t):
                    if ch in '([{⟨': d += 1
                    elif ch in ')]}⟩': d -= 1
                    elif d == 0 and t.startswith(':=', k): return t[:k]
                    elif d == 0 and re.match(r'\bwhere\b', t[k:]) and (k == 0 or not t[k-1].isalnum()):
                        return t[:k]
                return None
            j, buf = i, []
            while j < len(lines):
                buf.append(lines[j])
                c = cut(' '.join(buf))
                if c is not None or (j > i and lines[j+1:j+2] and re.match(r'^\s*\|[^|\n]*=>', lines[j+1])):
                    break
                j += 1
            t = ' '.join(buf)
            c = cut(t)
            t = c if c is not None else t
            t = re.sub(r'^@\[[^\]]*\]\s*', '', t.strip())
            out[full] = (m.group(3), i + 1, re.sub(r'\s+', ' ', t).strip())
            i = j + 1; continue
        i += 1
    return out
for f in files:
    old = subprocess.run(['git', 'show', f'{base}:{f}'], cwd=root, capture_output=True,
                         text=True).stdout
    new = open(f'{root}/{f}', encoding='utf-8').read()
    a, b = decls(old) if old else {}, decls(new)
    for n in sorted(set(a) | set(b)):
        if n in a and n not in b:
            print(f"REMOVED\t{f}:{a[n][1]}\t{n}\t{a[n][0]}\t{a[n][2]}")
        elif n in b and n not in a:
            print(f"ADDED\t{f}:{b[n][1]}\t{n}\t{b[n][0]}\t{b[n][2]}")
        elif a[n][2] != b[n][2]:
            print(f"CHANGED\t{f}:{a[n][1]}->{b[n][1]}\t{n}\t{b[n][0]}\t{a[n][2]}\t=>\t{b[n][2]}")
