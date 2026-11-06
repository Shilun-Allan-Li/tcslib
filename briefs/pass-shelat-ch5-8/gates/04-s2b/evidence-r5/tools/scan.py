"""Rule-10 source scan (gate 04 round 4).

scan.py <worktree> <files.txt> <constants.tsv> <candidate-dir> <seal-results.txt> <out.log> [--rev REV]

For every Lean file F: find every explicit `unfold X`, `delta X`, and every name X passed in the
lemma list of `rw`/`rwa`/`rewrite`/`erw`/`nth_rw`/`nth_rewrite`/`simp_rw`/`simp`/`simp only`/
`simp_all`/`simpa`/`dsimp`/`dsimp only`/`norm_num`/`field_simp`/`simp_arith`/`push_cast`, and
resolve X (namespace and `open` context of the line) against the table of TCSlib constants written
by the collector. A hit is an X that resolves to a definition (kind `def`, `def-reducible`,
`def-instance`) declared in another TCSlib module, or to a generated equation lemma
(`X.eq_N`/`X.eq_def`/`X.eq_unfold`) of such a definition. `show`/`change` steps are covered by the
seal (they are checked by definitional unification at default transparency, which the
`local irreducible` seal blocks); the scan lists every `show`/`change` that sits on a line where the
seal failed. The proof-term check of the collector (references to generated equation lemmas of a
foreign definition) is appended."""
import re, sys, os
from pathlib import Path
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import declx

WT, FILES, TABLE, CAND, SEALRES, OUT = sys.argv[1:7]
REV = sys.argv[sys.argv.index('--rev') + 1] if '--rev' in sys.argv else None
SRCLEM = sys.argv[sys.argv.index('--srclemmas') + 1] if '--srclemmas' in sys.argv else None
import subprocess
kinds, mods = {}, {}
for l in open(TABLE, encoding='utf-8'):
    p = l.rstrip('\n').split('\t')
    if len(p) == 3:
        kinds[p[0]] = p[1]; mods[p[0]] = p[2]

def strip_comments(src):
    """Blank out comments (nested block comments and docstrings, line comments) and string
    literals, keeping line structure."""
    out, i, depth, n = [], 0, 0, len(src)
    instr = False
    while i < n:
        c = src[i]
        if depth == 0 and not instr and src.startswith('--', i):
            j = src.find('\n', i); j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if not instr and src.startswith('/-', i):
            depth += 1; out.append('  '); i += 2; continue
        if depth > 0 and src.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2; continue
        if depth > 0:
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if c == '"' and (i == 0 or src[i - 1] != '\\'):
            instr = not instr; out.append(' '); i += 1; continue
        if instr:
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        out.append(c); i += 1
    return ''.join(out)

TAC = re.compile(r'(?<![\w.\'])(unfold|delta|rw|rwa|rewrite|erw|nth_rw|nth_rewrite|simp_rw|simp_all|simpa|simp|dsimp|norm_num|field_simp|simp_arith|push_cast|rw_mod_cast)(\??!?)(?![\w\'])')
IDENT = re.compile(r"[^\s,\[\]()⟨⟩:;{}←]+")

def bracket_list(text, k):
    """If a `[ ... ]` list starts at or after k (skipping `only`, config, `at` clauses are after),
    return (start, end) of its content."""
    m = re.compile(r'\s*(?:only\s*)?(?:\(config\s*:=[^)]*\)\s*)?(?:\(\s*\w+\s*:=[^)]*\)\s*)*(?:only\s*)?(?:\d+\s*)*\[').match(text, k)
    if not m:
        return None
    s = m.end(); d = 1; j = s
    while j < len(text) and d:
        if text[j] == '[': d += 1
        elif text[j] == ']': d -= 1
        j += 1
    return (s, j - 1)

def items(seg):
    out, d, cur, start = [], 0, '', 0
    for idx, ch in enumerate(seg):
        if ch in '([⟨{': d += 1
        elif ch in ')]⟩}': d -= 1
        if ch == ',' and d == 0:
            out.append((start, cur)); cur = ''; start = idx + 1
        else:
            cur += ch
    out.append((start, cur))
    return out

def head_ident(item):
    t = item.strip()
    t = re.sub(r'^(←|<-|↓|-|@|\(|\s)+', '', t)
    m = IDENT.match(t)
    return m.group(0).rstrip('.') if m else None

def resolve(tok, ns, opens, mymod):
    """Lean's order (Lean/ResolveName.lean, resolveGlobalName): the innermost namespace level with
    a match wins; otherwise the exact name, this module's private name and the open namespaces."""
    if tok.startswith('_root_.'):
        return [tok[7:]] if tok[7:] in kinds else []
    parts = ns.split('.') if ns else []
    for k in range(len(parts), 0, -1):
        p = '.'.join(parts[:k])
        hit = [x for x in (f"{p}.{tok}", f"_private.{mymod}.0.{p}.{tok}") if x in kinds]
        if hit:
            return hit
    res = [x for x in (tok, f"_private.{mymod}.0.{tok}") if x in kinds]
    for o in sorted(opens):
        full = f"{o}.{tok}"
        if full in kinds and full not in res:
            res.append(full)
    return res

EQN = re.compile(r'^(.*)\.(eq_\d+|eq_def|eq_unfold)$')

def classify(full, mymod):
    m = EQN.match(full)
    if m and m.group(1) in kinds:
        par = m.group(1)
        if mods[par] != mymod and kinds[par] in ('def', 'def-reducible', 'def-instance'):
            return ('eqn-lemma-of-foreign-def', par)
        return None
    if mods.get(full) != mymod and kinds.get(full) in ('def', 'def-irreducible', 'def-reducible', 'def-instance'):
        return ({'def': 'foreign-def', 'def-irreducible': 'foreign-def', 'def-reducible': 'foreign-abbrev',
                 'def-instance': 'foreign-instance'}[kinds[full]], full)
    return None

sealfail = {}
for l in open(SEALRES, encoding='utf-8'):
    m = re.match(r'\s+(\S+\.lean):(\d+):', l)
    if m: sealfail.setdefault(m.group(1), set()).add(int(m.group(2)))

DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|class|example|opaque)\b\s*(\S*)')

hits, shows, nshow = [], [], 0
srclem = {}
files = [l.strip() for l in open(FILES) if l.strip()]
for path in files:
    mymod = path[:-5].replace('/', '.')
    raw = (subprocess.run(['git', '-C', WT, 'show', f'{REV}:{path}'], capture_output=True, text=True).stdout
           if REV else (Path(WT) / path).read_text(encoding='utf-8'))
    src = strip_comments(raw)
    rawlines = raw.split('\n')
    lines = src.split('\n')
    exts = declx.extents(raw)
    # namespace / open context per line
    ctx, stack, opens_stack = [], [], [set()]
    for ln in lines:
        s = ln.strip()
        m = re.match(r'^namespace\s+(\S+)', s)
        if m:
            stack.append(('ns', m.group(1))); opens_stack.append(set(opens_stack[-1]))
        m2 = re.match(r'^section\b', s)
        if m2:
            stack.append(('sec', '')); opens_stack.append(set(opens_stack[-1]))
        m3 = re.match(r'^end\b', s)
        if m3 and stack:
            stack.pop(); opens_stack.pop()
        m4 = re.match(r'^open\s+(?:scoped\s+)?([^()\n]*?)(?:\s+in)?\s*$', s) or re.match(r'^open\s+(?:scoped\s+)?(.*?)\s+in\b', s)
        if m4:
            cur = '.'.join(x for k, x in stack if k == 'ns')
            for o in m4.group(1).split():
                if o in ('in', 'hiding', 'renaming') or '(' in o:
                    break
                opens_stack[-1].add(o)
                # an `open` inside a namespace may also name a sub-namespace of the current one
                parts = cur.split('.') if cur else []
                for k in range(len(parts), 0, -1):
                    opens_stack[-1].add('.'.join(parts[:k]) + '.' + o)
        ctx.append(('.'.join(x for k, x in stack if k == 'ns'), set(opens_stack[-1])))
    offs = [0]
    for ln in lines: offs.append(offs[-1] + len(ln) + 1)
    def lineof(pos):
        lo, hi = 0, len(offs) - 1
        while lo < hi:
            mid = (lo + hi + 1) // 2
            if offs[mid] <= pos: lo = mid
            else: hi = mid - 1
        return lo + 1
    def declof(ln):
        for j in range(ln - 1, -1, -1):
            m = DECL.match(rawlines[j])
            if m: return f"{m.group(1)} {m.group(2)}"
        return '?'
    for m in TAC.finditer(src):
        tac = m.group(1)
        ln = lineof(m.start())
        ns, opens = ctx[ln - 1]
        toks = []
        if tac in ('unfold', 'delta'):
            # names on the tactic's line and on following lines indented past the tactic's column
            col = m.start() - offs[ln - 1]
            cur, stop = ln, False
            seg = src[m.end():offs[ln] - 1] if ln < len(offs) else src[m.end():]
            while True:
                part = re.split(r'\bat\b|;|<;>|\)|\||=>|·', seg)
                for t in part[0].split():
                    if not re.match(r"^[^\s\d,\[\]()⟨⟩:;{}←][^\s,\[\]()⟨⟩:;{}←]*$", t):
                        stop = True; break
                    toks.append((t, cur))
                if stop or len(part) > 1 or cur >= len(lines):
                    break
                nxt = lines[cur]
                ind = len(nxt) - len(nxt.lstrip())
                if not nxt.strip() or ind <= col:
                    break
                cur += 1; seg = nxt
        else:
            br = bracket_list(src, m.end())
            if not br:
                continue
            s, e = br
            for (o, it) in items(src[s:e]):
                h = head_ident(it)
                if h:
                    toks.append((h, lineof(s + o + (len(it) - len(it.lstrip())))))
        for (t, tl) in toks:
            for full in resolve(t, ns, opens, mymod):
                if SRCLEM and kinds.get(full) == 'thm' and tac not in ('unfold', 'delta'):
                    ow = [e['name'] for e in exts if e['dstart'] <= tl <= e['end']]
                    srclem.setdefault(mymod, set()).add((ow[0] if ow else '?', full))
                c = classify(full, mymod)
                if c:
                    hits.append(f"{path}:{tl}\t{tac}\t{t}\t{c[0]}\t{c[1]}\t{mods[c[1]]}\t[{declof(tl)}]\t{rawlines[tl - 1].strip()[:140]}")
    for m in re.finditer(r'(?<![\w.\'])(show|change)(?![\w\'])', src):
        ln = lineof(m.start()); nshow += 1
        if ln in sealfail.get(path, set()):
            shows.append(f"{path}:{ln}\t{m.group(1)}\t[{declof(ln)}]\t{rawlines[ln - 1].strip()[:140]}")

eqn = []
for path in files:
    mymod = path[:-5].replace('/', '.')
    p = Path(CAND) / f"{mymod}.eqn.txt"
    if p.exists():
        eqn += [l.rstrip('\n') for l in open(p, encoding='utf-8') if l.strip()]

with open(OUT, 'w', encoding='utf-8') as o:
    o.write(f"# rule-10 source scan over {len(files)} files{(' at ' + REV) if REV else ''}; hit = name resolving to a definition of another TCSlib module\n")
    o.write("# file:line\ttactic\ttoken\tkind\tforeign definition\tits module\t[declaration]\tsource line\n")
    o.write(f"## (c1) unfold/delta/rw/simp/dsimp lemma-list hits: {len(hits)}\n")
    for h in hits: o.write(h + '\n')
    o.write(f"## (c2) show/change steps on a line where the seal failed: {len(shows)} (of {nshow} show/change occurrences, all checked by the seal)\n")
    for s in shows: o.write(s + '\n')
    o.write(f"## (c3) proof terms referring to a generated equation lemma of a foreign TCSlib definition (collector): {len(eqn)}\n")
    o.write("# module\towner declaration\tconstant\tequation lemma\n")
    for e in eqn: o.write(e + '\n')
if SRCLEM:
    os.makedirs(SRCLEM, exist_ok=True)
    for f in files:
        md = f[:-5].replace('/', '.')
        with open(os.path.join(SRCLEM, md + '.txt'), 'w', encoding='utf-8') as o:
            for (ow, lm) in sorted(srclem.get(md, ())): o.write(f"{ow}\t{lm}\n")
print(len(hits), 'lemma-list hits;', len(shows), 'show/change at seal failures;', len(eqn), 'proof-term equation-lemma refs')
