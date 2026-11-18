"""sweeprows.py <SP> <G> <head>: #210's final sweep rows tagged 195 against this round's seal evidence."""
import csv, re, sys
SP, G, H = sys.argv[1:4]
base = open(G + '/seal-control-base.log').read()
final = open(G + '/seal-evidence.log').read()
rows = [r for r in csv.reader(open(SP + '/e1/final5/final-reads.tsv'), delimiter='\t') if r[0] == '195']
out = [f"# #210's final sweep rows tagged 195 ($SP/e1/final5/final-reads.tsv, line numbers of #210's copies) against the evidence at {H}",
       "# file\tdeclaration\tkind\tforeign definitions (sweep)\tfinal seal (seal-evidence.log)\tcandidates at the head\tbase control (seal-control-base.log)"]
for r in rows:
    f, d, kind, fd = r[1], r[2], r[4], r[5]
    mod = f[:-5].replace('/', '.')
    cl = {l.split('\t')[0] for l in open(f"{G}/candidates/{mod}.txt") if l.strip() and not l.startswith('#')}
    names = fd.split(',')
    sealed = [n for n in names if n in cl]; other = [n for n in names if n not in cl]
    fl = re.search(re.escape(f) + r': .*', final).group(0)
    hit = re.search(r'\[\w+ ' + re.escape(d) + r'\]', base) is not None
    out.append(f"{f}\t{d}\t{kind}\t{fd}\t{'PASS' if ' PASS ' in fl else 'FAIL'}, no named entry\tsealed: {','.join(sealed) or '-'}; "
               f"not candidates: {','.join(other) or '-'}\t{'FAILS at this declaration' if hit else 'no error at this declaration'}")
open(G + '/sweep-rows.tsv', 'w').write('\n'.join(out) + '\n'); print('\n'.join(out[2:]))
