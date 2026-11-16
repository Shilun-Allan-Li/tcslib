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

ANC_B2 = '      (bb1Scheme G ℓ).encCT κ ⟨d, ⟨BB1.decodeT _ m * T, Z, Z ^ α₁.val⟩⟩ := rfl'


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
    Z, O, T = j(A[26:39]), j(A[40:53]), j(A[54:68])   # Defs readers zero / one / two
    B1last, B2 = A[96], j(A[98:109])                  # last line of block B1; block B2 text
    assert Z.startswith('/--') and O.startswith('/--') and T.startswith('/--')
    assert B2.startswith('/--') and B1last == '  exists_congr fun _ => List.ofFn_inj.symm'
    Zr = '\n\n' + Z + '\n'
    C = [
        ('M0-unmutated', D0, B0,
         dict(result='PASS', ok=7, diff={'Defs': (0, 0, 0), 'BonehBoyen': (0, 0, 0)})),
        ('M1a-char-in-reader-Defs',
         rep(D0, '    (x : (S.sidSpec κ).dom 2) (s : σ) :',
             '    (x : (S.sidSpec κ).dom 1) (s : σ) :'),
         B0, dict(result='FAIL', ok=6, textdiff=['oracleImpl_two_onSpec'], ndiff=1,
                  diff={'Defs': (0, 0, 1), 'BonehBoyen': (0, 0, 0)})),
        ('M1b-char-in-reader-BonehBoyen', D0,
         rep(B0, '  exists_congr fun _ => List.ofFn_inj.symm',
             '  exists_congr fun x => List.ofFn_inj.symm'),
         dict(result='FAIL', ok=6, textdiff=['bb1Scheme_msgSpace_iff'], ndiff=1,
              diff={'Defs': (0, 0, 0), 'BonehBoyen': (0, 0, 1)})),
        ('M2a-reader-deleted-Defs', rep(D0, Z + '\n\n' + O + '\n', Z + '\n'), B0,
         dict(result='FAIL', ok=6, missing=['oracleImpl_one_onSpec'],
              diff={'Defs': (0, 14, 0), 'BonehBoyen': (0, 0, 0)})),
        ('M2b-reader-deleted-BonehBoyen', D0,
         rep(B0, ANC_B2 + '\n\n' + B2 + '\n', ANC_B2 + '\n'),
         dict(result='FAIL', ok=6, missing=['ofFn_bb1SimCt'],
              diff={'Defs': (0, 0, 0), 'BonehBoyen': (0, 12, 0)})),
        ('M3a-extra-line-Defs', rep(D0, '\nend IBEScheme\n', '\n-- extra line\nend IBEScheme\n'),
         B0, dict(result='FAIL', ok=7, diff={'Defs': (1, 0, 0), 'BonehBoyen': (0, 0, 0)})),
        ('M3b-extra-line-BonehBoyen', D0,
         rep(B0, '\nsection Simulator\n', '\nsection Simulator\n\n'),
         dict(result='FAIL', ok=7, diff={'Defs': (0, 0, 0), 'BonehBoyen': (1, 0, 0)})),
        ('M4a-reader-moved-BonehBoyen', D0,
         rep(rep(B0, ANC_B2 + '\n\n' + B2 + '\n', ANC_B2 + '\n'),
             '\n' + B1last + '\n', '\n' + B1last + '\n\n' + B2 + '\n'),
         dict(result='FAIL', ok=6, moved=['ofFn_bb1SimCt'])),
        ('M4b-readers-reordered-Defs', rep(D0, Z + '\n\n' + O, O + '\n\n' + Z), B0,
         dict(result='FAIL', ok=5, moved=['oracleImpl_one_onSpec', 'oracleImpl_zero_onSpec'])),
        ('M5a-docstring-edited-BonehBoyen', D0,
         rep(B0, '/-- **The key encoding as a word**', '/-- **The key encoding as a string**'),
         dict(result='FAIL', ok=6, textdiff=['ofFn_bb1Scheme_encSK'], ndiff=1,
              diff={'Defs': (0, 0, 0), 'BonehBoyen': (0, 0, 1)})),
        ('M5b-docstring-edited-Defs',
         rep(D0, 'as two messages, its answer', 'as two strings, its answer'),
         B0, dict(result='FAIL', ok=6, textdiff=['oracleImpl_two_onSpec'], ndiff=1,
                  diff={'Defs': (0, 0, 1), 'BonehBoyen': (0, 0, 0)})),
        ('M6-reader-duplicated-Defs', rep(D0, '\nend IBEScheme\n', Zr + '\nend IBEScheme\n'), B0,
         dict(result='FAIL', ok=6, duplicate=['oracleImpl_zero_onSpec'])),
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
