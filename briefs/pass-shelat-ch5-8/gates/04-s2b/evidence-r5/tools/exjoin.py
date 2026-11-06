"""exjoin.py <declchanges.tsv> <unseal.json> <exclusions.md>: every declaration carrying an exclusion
(an unseal entry, section A, or an explicit-unfold row, section B) with its classifier status."""
import json, re, sys
st = {}
for l in open(sys.argv[1]):
    p = l.rstrip('\n').split('\t'); st[(p[0], p[1])] = p[4:]
un = json.load(open(sys.argv[2]))
hit = {}
for f, v in un.items():
    for e in v: hit.setdefault((f, e['decl']), [0, 0])[0] += len(e['names'])
sec = None
for l in open(sys.argv[3]):
    if l.startswith('## B'): sec = 'B'
    elif l.startswith('## D'): sec = 'D'
    elif l.startswith('## '): sec = None
    m = re.match(r"^\| `([^`]+\.lean)` \| `([^`]+)` \| \w+ \|", l)
    if m and (sec == 'B' or (sec == 'D' and '| explicit `' in l)):
        f = 'TCSlib/Cryptography/' + m.group(1); d = m.group(2)
        full = d if d.startswith(('Complexity.', 'TCSlib.')) else 'TCSlib.Cryptography.' + d
        hit.setdefault((f, full), [0, 0])[1] += 1
for (f, d), v in sorted(hit.items()):
    s = st.get((f, d), ['?'])
    if s[0] != 'SAME':
        print(f"{s[0]}\t{f.replace('TCSlib/Cryptography/', '')}\t{d.replace('TCSlib.Cryptography.', '')}\tA-names={v[0]}\tB-hits={v[1]}\t{' '.join(s[1:])}")
print(f"# {sum(1 for k in hit if st.get(k, ['?'])[0] != 'SAME')} of {len(hit)} declarations with exclusions are not SAME")
