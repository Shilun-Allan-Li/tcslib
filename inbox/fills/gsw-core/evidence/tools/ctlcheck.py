"""Check the paired seal controls (python3 -I).

usage: ctlcheck.py CONTROLS.lean UNSEALED_LOG RESULTS.jsonl
Each `-- CTL-<name>-<KIND>` comment starts a control that runs until the next tag or `end`.
Expectations per variant (errors counted in both `error:` and `error(` forms, with
-DmaxErrors=0, mapped back to source lines):
  unsealed: every control 0 errors;
  POS: 0 errors in every sealed variant;
  NEG: exactly 1 error in every sealed variant;
  COE: 0 errors in coe variants, exactly 1 in strict variants.
"""
import json, re, sys

src, unsealed, results = sys.argv[1:4]
lines = open(src).read().splitlines()
ctl = []
for i, l in enumerate(lines, 1):
    m = re.match(r'-- CTL-(\S+)-(POS|NEG|COE)$', l)
    if m:
        ctl.append([m[1], m[2], i, None])
    elif l.startswith('end ') and ctl and ctl[-1][3] is None:
        ctl[-1][3] = i - 1
for a, b in zip(ctl, ctl[1:]):
    a[3] = b[2] - 1
ERR = re.compile(r'^\S+\.lean:(\d+):\d+: error[:(].*$', re.M)


def owner(line):
    for name, kind, lo, hi in ctl:
        if lo <= line <= hi:
            return f'{name}-{kind}'
    return None


ok = True
raw = open(unsealed).read()
ue = [int(m[1]) for m in ERR.finditer(raw)]
print(f'unsealed: {len(ue)} error(s) {"OK" if not ue else "FAIL"}')
ok &= not ue
rows = [json.loads(l) for l in open(results)]
for r in rows:
    variant = f'{r["mode"]}_{r["variant"]}'
    counts = {}
    stray = 0
    for e in r['errors']:
        o = owner(e['source_line'])
        if o is None:
            stray += 1
        else:
            counts[o] = counts.get(o, 0) + 1
    bad = []
    for name, kind, lo, hi in ctl:
        n = counts.get(f'{name}-{kind}', 0)
        want = 0 if kind == 'POS' else 1 if kind == 'NEG' else (0 if r['variant'] == 'coe' else 1)
        if n != want:
            bad.append(f'{name}({kind}) got {n} want {want}')
    good = not bad and not stray and r['harness_valid']
    ok &= good
    print(f'{variant}: errors={len(r["errors"])} harness={r["harness_valid"]} '
          f'{r["install"]} per-control={counts} stray={stray} {"OK" if good else "FAIL " + str(bad)}')
print(f'controls: {len(ctl)} ({sum(k == "POS" for _, k, _, _ in ctl)} POS, '
      f'{sum(k == "NEG" for _, k, _, _ in ctl)} NEG, {sum(k == "COE" for _, k, _, _ in ctl)} COE)')
print('CONTROLS ' + ('ALL_OK' if ok else 'FAIL'))
sys.exit(0 if ok else 1)
