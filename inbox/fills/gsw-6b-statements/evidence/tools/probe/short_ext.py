"""short_ext.py <new-names.tsv> <src-root>... (gsw-6b-statements, sub-agent probe; new; check 11 (b)): for every new
short name (last component), the declarations with that last component in the given source trees (Mathlib,
Batteries, the toolchain's core `src/lean`), found by a keyword regex
`(def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque|axiom) (<ns>.)?<short>` on source lines.
Textual: namespaces of the hits are not resolved (the hit line is printed)."""
import sys, os, re, collections
newf = sys.argv[1]; roots = sys.argv[2:]
shorts = sorted({l.split('\t')[0].split('.')[-1] for l in open(newf) if not l.startswith('#') and l.strip()})
pat = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|noncomputable|nonrec|partial|unsafe|scoped)\s+)*'
                 r'(?:def|theorem|lemma|abbrev|structure|class|inductive|instance|opaque|axiom)\s+(?:[\w.]*\.)?([^\s.(:{\[]+)')
want = set(shorts); hits = collections.defaultdict(list)
for root in roots:
    for dp, dn, fn in os.walk(root):
        for f in fn:
            if not f.endswith('.lean'): continue
            p = os.path.join(dp, f)
            try: lines = open(p, encoding='utf-8', errors='replace').read().split('\n')
            except OSError: continue
            for i, l in enumerate(lines, 1):
                m = pat.match(l)
                if m and m.group(1) in want: hits[m.group(1)].append(f'{p}:{i}: {l.strip()[:110]}')
print(f'# {len(shorts)} new short names; roots: {roots}')
for s in shorts:
    if hits[s]:
        print(f'EXT\t{s}\t{len(hits[s])} hits')
        for h in hits[s][:6]: print(f'\t{h}')
print(f'RESULT short_names_with_external_hits={sum(1 for s in shorts if hits[s])}')
