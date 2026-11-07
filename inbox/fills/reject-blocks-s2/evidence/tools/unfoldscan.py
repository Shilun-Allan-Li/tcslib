#!/usr/bin/env python3
"""Explicit-unfold scan of the touched declarations (text level).

For each touched declaration block of the HEAD source (raw text, comments kept so that
blank/comment-only continuation lines are traversed), find every `simp`, `simp only`, `simp_all`,
`simpa`, `dsimp`, `rw`, `rewrite`, `rwa`, `erw`, `nth_rewrite`/`nth_rw`, `unfold`, `delta`,
`simp_rw`, `field_simp`, `norm_num [..]` occurrence and extract its argument identifiers: a
bracketed list is read to its balanced `]` across any number of lines (comments inside are
removed); `unfold`/`delta` read identifiers to the end of the tactic (line end, `;`, `at`, `<;>`).
Output JSON: {module: {decl: [identifiers]}} and the union of identifiers."""
import re, json, sys
F = '/workspace/tcslib-fill/TCSlib/Cryptography/Candidates/'
touched = json.load(open('/workspace/s2-evidence/logs/touched.json'))
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec)\s+)*"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|example)\b\s*([^\s(:{\[]*)")
BOUND = re.compile(r"^(/--|/-!|section|end|namespace|open|variable|attribute|set_option|omit|include|#)")
KW = re.compile(r"(?<![\w.'])(simp_all|simp_rw|simpa|simp|dsimp|field_simp|norm_num|rwa|rewrite|erw|rw|nth_rewrite|nth_rw|unfold|delta)\b")
IDENT = re.compile(r"[A-Za-z_\u03b1-\u03c9\u0391-\u03a9][\w.'?!\u2080-\u2089\u03b1-\u03c9]*")

def strip_comments_keep_len(s):
    out = []; i = 0; n = len(s); depth = 0
    while i < n:
        if s.startswith('/-', i): depth += 1; out.append('  '); i += 2; continue
        if depth:
            if s.startswith('-/', i): depth -= 1; out.append('  '); i += 2
            else: out.append('\n' if s[i] == '\n' else ' '); i += 1
            continue
        if s.startswith('--', i):
            j = s.find('\n', i); j = n if j < 0 else j; out.append(' ' * (j - i)); i = j; continue
        out.append(s[i]); i += 1
    return ''.join(out)

res = {}; union = set(); counts = {}
for mod, names in touched.items():
    f = mod.split('.')[-1]
    raw = open(F + f + '.lean').read()
    code = strip_comments_keep_len(raw)
    lines = code.split('\n')
    starts = [(i, m.group(2)) for i, l in enumerate(lines) if (m := DECL.match(l))]
    res[f] = {}
    for k, (i, name) in enumerate(starts):
        if name not in names: continue
        j = starts[k + 1][0] if k + 1 < len(starts) else len(lines)
        # stop at a column-0 boundary command
        for t in range(i + 1, j):
            if lines[t] and not lines[t][0].isspace() and BOUND.match(raw.split('\n')[t]):
                j = t; break
        body = '\n'.join(lines[i:j])
        ids = []; occ = 0
        for m in KW.finditer(body):
            occ += 1
            p = m.end(); kw = m.group(1)
            if kw in ('unfold', 'delta'):
                e = len(body)
                for stop in ['\n', ';', '<;>', ' at ']:
                    q = body.find(stop, p)
                    if q >= 0: e = min(e, q)
                ids += IDENT.findall(body[p:e]); continue
            # skip `only`, config, `at`-less forms; find the next '[' before a newline-terminated tactic end
            q = p
            while q < len(body) and body[q] in ' \t': q += 1
            if body.startswith('only', q): q += 4
            while q < len(body) and body[q] in ' \t\n': q += 1
            if q >= len(body) or body[q] != '[': continue
            depth = 0; e = q
            while e < len(body):
                if body[e] == '[': depth += 1
                elif body[e] == ']':
                    depth -= 1
                    if depth == 0: break
                e += 1
            inner = body[q + 1:e]
            for item in re.split(r',', inner):
                item = item.strip().lstrip('←').strip()
                item = re.sub(r'^-\s*', '', item)
                mm = IDENT.match(item)
                if mm: ids.append(mm.group(0))
        res[f][name] = sorted(set(ids)); counts[f + '.' + name] = occ
        union |= set(ids)
json.dump({'per_decl': res, 'tactic_occurrences': counts, 'union': sorted(union)},
          open(sys.argv[1], 'w'), indent=1, ensure_ascii=False)
print(len(union), 'distinct identifiers;', sum(counts.values()), 'tactic occurrences')
print(sorted(union))
