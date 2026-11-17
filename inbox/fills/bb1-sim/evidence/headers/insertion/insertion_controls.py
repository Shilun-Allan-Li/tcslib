# ADAPTED (bb1-sim, lead, 2026-11-17) from T4's evidence/headers/insertion/insertion_controls.py
# (exchange inbox/fills/bb1-machine, f14ac810). Changes: the control mutations are re-targeted to
# the ten bb1-sim readers (same twelve control kinds; the expected counts follow from the
# readers' lengths); the docstring below is T4's, read with these changes.
"""insertion_controls.py <base-Defs> <head-Defs> <base-BonehBoyen> <head-BonehBoyen> <readers.txt>
                        <checker> <outdir>

Mutation controls of insertion_check.py (fill bb1-machine). Run as `python3 -I`. For each control
it writes the (possibly mutated) head files to <outdir>/<control>/{Defs,BonehBoyen}.lean, runs the
checker on them against the unchanged base files, saves the checker's output as
<outdir>/<control>/check.out and asserts the expected result:
  M0  unmutated heads                                       -> PASS, every count 0
  M1a one character changed in a reader's statement (Defs) -> FAIL, exactly one differing line
  M1b one character changed in a reader's proof (BonehBoyen)-> FAIL, exactly one differing line
  M2a one reader deleted (oracleImpl_one_onSpec, docstring and leading blank line)
                                                            -> FAIL, exactly one reader removed
  M2b one reader deleted (ofFn_bb1SimCt, the whole block B2)-> FAIL, exactly one reader removed
  M3a one extra line in Defs.lean outside the blocks        -> FAIL (readers intact)
  M3b one extra line in BonehBoyen.lean outside the blocks  -> FAIL (readers intact)
  M4a ofFn_bb1SimCt moved to right after the simps block    -> FAIL, reader MOVED
  M4b oracleImpl_zero_onSpec and _one_onSpec swapped        -> FAIL, both MOVED
  M5a a reader's docstring edited (ofFn_bb1Scheme_encSK)    -> FAIL, one differing line
  M5b a reader's docstring edited (oracleImpl_two_onSpec)   -> FAIL, one differing line
  M6  a reader duplicated (extra copy in Defs.lean)         -> FAIL, reader DUPLICATE
Every mutation is a single-occurrence edit (asserted). Prints one line per control and
`ALL_CONTROLS_OK True|False` (exit 0/1).

written by tools-agent (sub-agent), fill bb1-machine
"""
import ast
import os
import re
import subprocess
import sys



def read(p):
    with open(p, 'rb') as fh:
        return fh.read().decode('utf-8')


def write(p, s):
    with open(p, 'wb') as fh:
        fh.write(s.encode('utf-8'))


def rep(s, old, new):
    assert s.count(old) == 1, (old[:80], s.count(old))
    return s.replace(old, new)


def parse(out):
    r = {'result': None, 'readers': None, 'diff': {}}
    for ln in out.splitlines():
        if ln.startswith('RESULT '):
            r['result'] = ln.split()[1]
        m = re.match(r'READERS ok=(\d+) missing=(\[.*?\]) duplicate=(\[.*?\]) moved=(\[.*?\]) '
                     r'textdiff=(\[.*?\])$', ln)
        if m:
            r['readers'] = dict(ok=int(m.group(1)), missing=ast.literal_eval(m.group(2)),
                                duplicate=ast.literal_eval(m.group(3)),
                                moved=ast.literal_eval(m.group(4)),
                                textdiff=ast.literal_eval(m.group(5)))
        m = re.match(r'DIFF_VS_EXPECTED (\S+) added=(\d+) removed=(\d+) changed=(\d+)$', ln)
        if m:
            r['diff'][m.group(1)] = tuple(int(m.group(k)) for k in (2, 3, 4))
    return r


def main(argv):
    if len(argv) != 8:
        print(__doc__)
        return 2
    bD, hD, bB, hB, src, chk, out = argv[1:8]
    os.makedirs(out, exist_ok=True)
    D0, B0 = read(hD), read(hB)
    A = read(src).split('\n')
    j = '\n'.join
    Z, T2, O1 = j(A[0:13]), j(A[14:27]), j(A[28:38])   # sidImpl_zero_onSpec / two_onSpec / one_onQuery
    O2 = j(A[39:49])                                     # sidImpl_two_onQuery
    BE, BC = j(A[109:123]), j(A[124:131])                # bb1Scheme_enc_bind / ofFn_bb1Scheme_encCT
    assert all(x.startswith('/--') for x in (Z, T2, O1, O2, BE, BC)), 'block layout'
    assert 'theorem sidImpl_two_onQuery' in O2 and 'theorem ofFn_bb1Scheme_encCT' in BC
    assert 'theorem bb1Scheme_enc_bind' in BE
    Zr = '\n\n' + Z + '\n'
    C = [
        ('M0-unmutated', D0, B0,
         dict(result='PASS', ok=10, diff={'Defs': (0, 0, 0), 'BonehBoyen': (0, 0, 0)})),
        ('M1a-char-in-reader-Defs',
         rep(D0, O1, O1.replace('Fin (S.idLen.eval κ) → Bool) s := rfl',
                                'Fin (S.idLen.eval κ) → Bool) s := (rfl)')),
         B0, dict(result='FAIL', ok=9, textdiff=['sidImpl_one_onQuery'], ndiff=1,
                  diff={'Defs': (0, 0, 1), 'BonehBoyen': (0, 0, 0)})),
        ('M1b-char-in-reader-BonehBoyen', D0,
         rep(B0, '  simp only [bb1Scheme_keyGen, OracleComp.bind_assoc, OracleComp.pure_bind]',
             '  simp only [bb1Scheme_keyGen, OracleComp.bind_assoc, OracleComp.pure_bind ]'),
         dict(result='FAIL', ok=9, textdiff=['bb1Scheme_keyGen_bind'], ndiff=1,
              diff={'Defs': (0, 0, 0), 'BonehBoyen': (0, 0, 1)})),
        ('M2a-reader-deleted-Defs', rep(D0, O1 + '\n\n' + O2 + '\n', O1 + '\n'), B0,
         dict(result='FAIL', ok=9, missing=['sidImpl_two_onQuery'],
              diff={'Defs': (0, 11, 0), 'BonehBoyen': (0, 0, 0)})),
        ('M2b-reader-deleted-BonehBoyen', D0, rep(B0, BE + '\n\n' + BC + '\n', BE + '\n'),
         dict(result='FAIL', ok=9, missing=['ofFn_bb1Scheme_encCT'],
              diff={'Defs': (0, 0, 0), 'BonehBoyen': (0, 8, 0)})),
        ('M3a-extra-line-Defs', rep(D0, '\nend IBEScheme\n', '\n-- extra line\nend IBEScheme\n'),
         B0, dict(result='FAIL', ok=10, diff={'Defs': (1, 0, 0), 'BonehBoyen': (0, 0, 0)})),
        ('M3b-extra-line-BonehBoyen', D0,
         rep(B0, '\nsection Simulator\n', '\nsection Simulator\n\n'),
         dict(result='FAIL', ok=10, diff={'Defs': (0, 0, 0), 'BonehBoyen': (1, 0, 0)})),
        ('M4a-reader-moved-BonehBoyen', D0,
         rep(rep(B0, BE + '\n\n' + BC + '\n', BE + '\n'), '\nsection Simulator\n',
             '\n' + BC + '\n\nsection Simulator\n'),
         dict(result='FAIL', ok=9, moved=['ofFn_bb1Scheme_encCT'])),
        ('M4b-readers-reordered-Defs', rep(D0, Z + '\n\n' + T2, T2 + '\n\n' + Z), B0,
         dict(result='FAIL', ok=8, moved=['sidImpl_two_onSpec', 'sidImpl_zero_onSpec'])),
        ('M5a-docstring-edited-BonehBoyen', D0,
         rep(B0, '/-- **The ciphertext encoding as a word**',
             '/-- **The ciphertext encoding as a string**'),
         dict(result='FAIL', ok=9, textdiff=['ofFn_bb1Scheme_encCT'], ndiff=1,
              diff={'Defs': (0, 0, 0), 'BonehBoyen': (0, 0, 1)})),
        ('M5b-docstring-edited-Defs',
         rep(D0, 'type is the call on the query read as two `msgLen(κ)`-bit messages',
             'type is the call on the query read as two `msgLen(κ)`-bit strings'),
         B0, dict(result='FAIL', ok=9, textdiff=['sidImpl_two_onQuery'], ndiff=1,
                  diff={'Defs': (0, 0, 1), 'BonehBoyen': (0, 0, 0)})),
        ('M6-reader-duplicated-Defs', rep(D0, '\nend IBEScheme\n', Zr + '\nend IBEScheme\n'), B0,
         dict(result='FAIL', ok=9, duplicate=['sidImpl_zero_onSpec'])),
    ]
    allok = True
    for name, d, b, exp in C:
        cd = os.path.join(out, name)
        os.makedirs(cd, exist_ok=True)
        pd, pb = os.path.join(cd, 'Defs.lean'), os.path.join(cd, 'BonehBoyen.lean')
        write(pd, d)
        write(pb, b)
        r = subprocess.run([sys.executable, '-I', chk, bD, pd, bB, pb, src],
                           capture_output=True, text=True)
        write(os.path.join(cd, 'check.out'), r.stdout + r.stderr)
        p = parse(r.stdout)
        rd = p['readers'] or {}
        why = []
        if p['result'] != exp['result']:
            why.append(f'result {p["result"]}')
        if (r.returncode == 0) != (exp['result'] == 'PASS'):
            why.append(f'rc {r.returncode}')
        if rd.get('ok') != exp['ok']:
            why.append(f'readers ok {rd.get("ok")}')
        for k in ('missing', 'duplicate', 'moved', 'textdiff'):
            if sorted(rd.get(k, [])) != sorted(exp.get(k, [])):
                why.append(f'{k} {rd.get(k)}')
        for f, t in exp.get('diff', {}).items():
            if p['diff'].get(f) != t:
                why.append(f'diff {f} {p["diff"].get(f)} != {t}')
        if 'ndiff' in exp:
            m = re.findall(r'TEXT DIFFERS \((\d+) line', r.stdout)
            if m != [str(exp['ndiff'])]:
                why.append(f'text-differs lines {m}')
        ok = not why
        allok &= ok
        print(f'{name}: {"OK" if ok else "UNEXPECTED"} | checker {p["result"]} rc={r.returncode}'
              f' | READERS ok={rd.get("ok")} missing={rd.get("missing")} '
              f'dup={rd.get("duplicate")} moved={rd.get("moved")} textdiff={rd.get("textdiff")}'
              f' | DIFF_VS_EXPECTED {p["diff"]}' + (f' | MISMATCH: {why}' if why else ''))
    print('ALL_CONTROLS_OK', allok)
    return 0 if allok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv))
