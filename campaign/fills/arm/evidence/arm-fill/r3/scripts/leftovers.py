"""R2-8: round-1 finding 11's leftovers, base against landed (text checks): the SpaceComplexity
facade's lines over 100 columns; a "Proof sketch." in the docstring of numVars_le_length_serialize,
reflTransGen_stepRel and nz_run; TQBFHardVerifier's Main-results bullet for predB_iff (declared in
TQBFHardBridge). usage: python3 -I leftovers.py <base-root> <landed-root>"""
import os, re, sys
roots = dict(zip(['base', 'landed'], sys.argv[1:3]))
C = 'TCSlib/Complexity/'
SK = [('ClassPSPACE/TQBFHardTseitin.lean', 'numVars_le_length_serialize'), ('ClassPSPACE/TQBFHardMachine.lean', 'reflTransGen_stepRel'),
      ('SpaceComplexity/ExpBFS/Run.lean', 'nz_run')]
def sketch(txt, name):
    m = re.search(r'^(?:theorem|lemma) ' + re.escape(name) + r'\b', txt, re.M)
    if not m: return None
    head = txt[:m.start()]; j = head.rfind('/--'); k = head.rfind('-/')
    # the docstring attached to the declaration: the last `/-- ... -/` before it, followed only by whitespace
    doc = head[j:k] if 0 <= j < k and not head[k + 2:].strip() else ''
    return 'Proof sketch.' in doc, txt.count('\n', 0, m.start()) + 1
for t, r in roots.items():
    rd = lambda p: open(os.path.join(r, C + p), encoding='utf-8').read()
    fac = [(i, len(l)) for i, l in enumerate(rd('SpaceComplexity.lean').split('\n'), 1) if len(l) > 100]
    print(f'{t}: SpaceComplexity.lean lines over 100 columns: {fac or "none"}')
    for p, n in SK:
        s, line = sketch(rd(p), n); print(f'{t}: {p}:{line} {n}: docstring has "Proof sketch.": {s}')
    v = [i for i, l in enumerate(rd('ClassPSPACE/TQBFHardVerifier.lean').split('\n'), 1) if re.match(r'\* `Complexity\.TQBFHard\.predB_iff`', l)]
    b = [i for i, l in enumerate(rd('ClassPSPACE/TQBFHardBridge.lean').split('\n'), 1) if re.match(r'\* `Complexity\.TQBFHard\.predB_iff`', l)]
    print(f'{t}: Main-results bullet for predB_iff: TQBFHardVerifier lines {v or "none"}; TQBFHardBridge lines {b or "none"}')
