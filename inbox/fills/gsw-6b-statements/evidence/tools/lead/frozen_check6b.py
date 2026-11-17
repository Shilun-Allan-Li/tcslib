"""frozen_check6b.py <repo> <base> <head> [--control-alter FILE:NAME] [--control-delete FILE:NAME]
(gsw-6b-statements, new; the 6a statement job's frozen_check.py depended on its seal harness's
declaration cutter, so this is a self-contained re-implementation of the same check 8.)
For each changed existing Lean file (git diff --name-only <base> <head>, files present at <base>):
(1) every declaration is cut out of the base and head texts (from its doc comment or attribute line
at column 0, or its declaration line, to the line before the next such start or top-level command)
and compared byte for byte; a base declaration missing at head is REMOVED, one changed is CHANGED
(header = up to the top-level `:=`/`where`, reported separately as HEADER), a head declaration not
at base is ADDED; (2) the non-declaration text is compared line by line (difflib): for BitEncoding
only inserted lines are allowed; for the facades GSW.lean and LWE.lean only `import` lines and lines
inside the module docstring may change. ALLOWED lists O2's five new declarations. A control
alters one character of NAME's header (`:` after the name -> ` :`) or deletes NAME in memory; the
controls must report exactly one difference / one removal."""
import sys, re, subprocess, difflib
repo, base, head = sys.argv[1:4]
rest = sys.argv[4:]
ctrl_alter = ctrl_del = None
i = 0
while i < len(rest):
    if rest[i] == '--control-alter': ctrl_alter = rest[i + 1]; i += 2
    elif rest[i] == '--control-delete': ctrl_del = rest[i + 1]; i += 2
    else: sys.exit('bad arg ' + rest[i])
ALLOWED = {('TCSlib/Cryptography/LWE/BitEncoding.lean', n) for n in
           ['decodeLo', 'decodeLo_eq', 'decodeHi', 'decodeHi_eq', 'decode_iff_mem_Ico']}
FACADES = {'TCSlib/Cryptography/LWE.lean', 'TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW.lean'}
INSERT_ONLY = {'TCSlib/Cryptography/LWE/BitEncoding.lean'}
KW = r'(theorem|lemma|def|abbrev|structure|inductive|instance|class|opaque|axiom)'
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  + KW + r'\s+([^\s(:{\[]+)')
TOP = re.compile(r'^(namespace|end|section|open|variable|universe|set_option|attribute|mutual|#|example|import|/-!)')
def git(*a): return subprocess.run(['git', '-C', repo] + list(a), capture_output=True, text=True, check=True).stdout
def cut(text):
    L = text.split('\n'); starts = []
    k = 0
    while k < len(L):
        if L[k].startswith('/--'):
            j = k
            while '-/' not in L[j]: j += 1
            m = j + 1
            while m < len(L) and L[m].startswith('@['): m += 1
            if m < len(L) and DECL.match(L[m]): starts.append((k, DECL.match(L[m]).group(2))); k = m + 1; continue
            k = j + 1; continue
        if L[k].startswith('@[') or DECL.match(L[k]):
            m = k
            while m < len(L) and L[m].startswith('@['): m += 1
            if m < len(L) and DECL.match(L[m]): starts.append((k, DECL.match(L[m]).group(2))); k = m + 1; continue
        k += 1
    out = {}; spans = []
    for idx, (s, name) in enumerate(starts):
        e = starts[idx + 1][0] if idx + 1 < len(starts) else len(L)
        j = s + 1
        while j < e:
            if TOP.match(L[j]) or (L[j].startswith('/--') and j > s and not L[s].startswith('/--')): break
            j += 1
        while j > s and L[j - 1].strip() == '': j -= 1
        out[name] = '\n'.join(L[s:j]); spans.append((s, j))
    rest = [l for n, l in enumerate(L) if not any(a <= n < b for a, b in spans)]
    return out, rest
def header(t):
    m = re.search(r':=|\bwhere\b', t[t.find('-/') + 2 if t.startswith('/--') else 0:])
    return t[:m.start() + (t.find('-/') + 2 if t.startswith('/--') else 0)] if m else t
files = [f for f in git('diff', '--name-only', base, head, '--', '*.lean').split()
         if subprocess.run(['git', '-C', repo, 'cat-file', '-e', f'{base}:{f}'], capture_output=True).returncode == 0]
viol = ndiff = nrem = 0
for f in files:
    old, new = git('show', f'{base}:{f}'), git('show', f'{head}:{f}')
    if ctrl_alter and ctrl_alter.split(':')[0] == f:
        name = ctrl_alter.split(':')[1]; d = cut(new)[0][name]
        pos = new.index(d); q = new.index(name + ' ', pos) + len(name)
        new = new[:q] + ' ' + new[q:]
    if ctrl_del and ctrl_del.split(':')[0] == f:
        name = ctrl_del.split(':')[1]; new = new.replace(cut(new)[0][name] + '\n', '', 1)
    a, ra = cut(old); b, rb = cut(new)
    print(f'== {f}: base {len(a)} declarations, head {len(b)}')
    for n in sorted(set(a) | set(b)):
        if n not in b: print(f'VIOLATION REMOVED\t{n}'); viol += 1; nrem += 1
        elif n not in a:
            ok = (f, n) in ALLOWED
            print(f"{'ADDED(allowed)' if ok else 'VIOLATION ADDED'}\t{n}"); viol += not ok
        elif header(a[n]) != header(b[n]): print(f'VIOLATION HEADER\t{n}'); viol += 1; ndiff += 1
        elif a[n] != b[n]: print(f'VIOLATION BODY\t{n}'); viol += 1; ndiff += 1
        else: print(f'IDENTICAL\t{n}')
    # non-declaration text
    sm = difflib.SequenceMatcher(a=ra, b=rb, autojunk=False)
    doc_start = next((k for k, l in enumerate(ra) if l.startswith('/-!')), -1)
    doc_end_old = next((k for k in range(max(doc_start, 0), len(ra)) if '-/' in ra[k]), -1)
    for op, i1, i2, j1, j2 in sm.get_opcodes():
        if op == 'equal': continue
        lines_old, lines_new = ra[i1:i2], rb[j1:j2]
        if f in INSERT_ONLY:
            ok = op == 'insert'
        elif f in FACADES:
            in_doc = doc_start >= 0 and doc_start < i1 and i2 <= doc_end_old
            ok = all(l.startswith('import ') or l.strip() == '' for l in lines_old + lines_new) or \
                 in_doc or (op == 'insert' and doc_start < i1 <= doc_end_old)
        else:
            ok = False
        tag = 'TEXT(allowed)' if ok else 'VIOLATION TEXT'
        print(f'{tag}\t{op}\t-{i1+1}..{i2} +{j1+1}..{j2}\t' + ' | '.join((lines_old + lines_new)[:3])[:150])
        viol += not ok; ndiff += (op != 'insert')
print(f'RESULT files={len(files)} violations={viol} differences={ndiff} removals={nrem}')
