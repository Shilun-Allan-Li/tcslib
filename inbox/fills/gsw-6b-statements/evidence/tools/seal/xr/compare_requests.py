r"""compare_requests.py <old-run-dir> <new-run-dir> [...more old/new pairs] (gsw-6b-statements sub-agent `seal`, new):
for every seal record present in both runs (same probe label, variant directories seals-A/B/coeA/coeB), compares the
requested constant lists (spelling + home) and the excluded elaborated-term rows; prints one line per probe with
`same`/`DIFFERENT` (+/− names), the source sha256 of both, and `RESULT different=<n> compared=<n>`."""
import sys, os, json, glob
args = sys.argv[1:]; diff = 0; comp = 0
for old, new in zip(args[0::2], args[1::2]):
    for V in ('A', 'B', 'coeA', 'coeB'):
        for p in sorted(glob.glob(os.path.join(new, 'seal', f'seals-{V}', '*.json'))):
            if p.endswith('manifest.json'): continue
            q = os.path.join(old, 'seal', f'seals-{V}', os.path.basename(p))
            if not os.path.exists(q): print(f'ONLY-NEW\t{V}\t{os.path.basename(p)}'); continue
            a, b = json.load(open(q)), json.load(open(p)); comp += 1
            ra = {(r['spelling'], r['home']) for r in a['rows']}; rb = {(r['spelling'], r['home']) for r in b['rows']}
            same = ra == rb and a['term_excluded'] == b['term_excluded']
            diff += not same
            extra = '' if same else f"\t+{sorted(rb - ra)} -{sorted(ra - rb)} terms_old={a['term_excluded']} terms_new={b['term_excluded']}"
            print(f"{'same' if same else 'DIFFERENT'}\t{V}\t{b['label']}\trequests {len(ra)}->{len(rb)}\t"
                  f"src {a['source_sha256'][:12]}->{b['source_sha256'][:12]}{extra}")
print(f'RESULT different={diff} compared={comp}')
