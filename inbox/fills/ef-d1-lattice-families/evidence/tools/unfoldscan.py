"""unfoldscan.py <defs.tsv> <file.lean>...: list every identifier passed to simp/rw/unfold/delta/
simp_rw/dsimp (inside their [...] lists or after unfold/delta) that names a foreign TCSlib definition
of the import closure (first column of defs.tsv, matched by full name or by a dotted suffix)."""
import re, sys
defs = [l.split('\t')[0] for l in open(sys.argv[1], encoding='utf-8') if l.strip()]
def foreign(tok):
    tok = tok.lstrip('←').strip()
    return [d for d in defs if d == tok or d.endswith('.' + tok)]
hits, total = [], 0
for f in sys.argv[2:]:
    txt = open(f, encoding='utf-8').read()
    for m in re.finditer(r'\b(simp only|simp_rw|simp|rw|rwa|nth_rewrite|dsimp only|dsimp|simpa only|simpa|erw)\b\s*(\[[^\]]*\])', txt):
        for tok in re.split(r'[,\s]+', m.group(2).strip('[]')):
            tok = tok.strip()
            if not tok: continue
            total += 1
            fd = foreign(tok)
            if fd: hits.append((f, txt[:m.start()].count('\n') + 1, m.group(1), tok, fd))
    for m in re.finditer(r'\b(unfold|delta)\s+([^\n]*)', txt):
        for tok in m.group(2).split():
            total += 1
            fd = foreign(tok)
            if fd: hits.append((f, txt[:m.start()].count('\n') + 1, m.group(1), tok, fd))
for h in hits: print(*h, sep='\t')
print(f'tokens scanned: {total}; foreign TCSlib definitions passed: {len(hits)}')
