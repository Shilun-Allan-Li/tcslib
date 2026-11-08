#!/usr/bin/env python3
"""Run whole-file seals for a list of owned modules at a revision, serially (one Lean process).
python3 -I sealrun.py <phase> <rev> <closure-log> <modules-file (paths without .lean)>
Probe: .lake/cleanup-part2-probes/seal/<phase>/<path>.lean ; logs via chk.py (CHK_PHASE=seal-<phase>).
Writes evidence/logs/seal-<phase>.json with per-module validity, counts and failing declarations."""
import sys, os, re, json, subprocess
phase, rev, clog, mods = sys.argv[1:5]
CLONE = '/workspace/cp2/src'; EV = '/workspace/cp2/evidence/logs'
DECL = re.compile(r"^(?:@\[[^\]]*\]\s*)*(?:(?:private|protected|noncomputable|nonrec|partial|unsafe)\s+)*"
                  r"(theorem|lemma|def|instance|structure|inductive|abbrev|class|example|opaque|axiom)\b\s*([^\s(:{\[]*)")
res = {}
out = f'{EV}/seal-{phase}.json'
if os.path.exists(out): res = json.load(open(out))
for path in [l.strip() for l in open(mods) if l.strip()]:
    if path in res and res[path].get('valid') is not None: continue
    mod = path.replace('/', '.')
    src = subprocess.run(['git', '-C', CLONE, 'show', f'{rev}:{path}.lean'], capture_output=True, text=True, check=True).stdout
    rel = f'.lake/cleanup-part2-probes/seal/{phase}/{path}'
    os.makedirs(os.path.dirname(f'{CLONE}/{rel}'), exist_ok=True)
    tmp = f'{CLONE}/{rel}.orig'
    open(tmp, 'w').write(src)
    subprocess.run(['python3', '-I', '/workspace/cp2/tools/mkseal.py', clog, mod, tmp, f'{CLONE}/{rel}.lean'], check=True, capture_output=True)
    os.remove(tmp)
    env = dict(os.environ, CHK_PHASE=f'seal-{phase}')
    r = subprocess.run(['python3', '-I', '/workspace/cp2/tools/chk.py', rel], env=env, capture_output=True, text=True)
    print(r.stdout.strip(), flush=True)
    log = open(f'{EV}/seal-{phase}/modules/{rel}.log').read()
    sealed = open(f'{CLONE}/{rel}.lean').read().split('\n')
    end = next(i for i, l in enumerate(sealed) if l == '-- CP2 END SEAL') + 1
    req = int(re.search(r'SEAL \(evidence probe; not library source\): (\d+) requests', '\n'.join(sealed)).group(1))
    chunks = re.findall(r'CP2-SEAL chunk=\d+ requested=(\d+) active=(\d+) already=(\d+)', log)
    errs = [(int(a), b) for a, b in re.findall(r'\.lean:(\d+):\d+: error[^:]*: ?(.*)', log)]
    harness = [e for e in errs if e[0] <= end] + [(0, m) for m in re.findall(r'CP2-SEAL (?:missing|no home|wrong home|wrong kind|not installed)[^\n]*', log)]
    eof = 'CP2-EOF' in log
    starts = [(i + 1, m.group(2) or f'<anonymous {m.group(1)}>') for i, l in enumerate(sealed) if (m := DECL.match(l))]
    failing = []
    for ln, msg in errs:
        if ln <= end: continue
        d = max((s for s in starts if s[0] <= ln), default=(0, '?'))
        failing.append({'decl': d[1], 'decl_line_in_probe': d[0], 'decl_line_in_source': d[0] - (sealed.count('') * 0) , 'error_line': ln, 'message': msg[:160]})
    valid = (not harness) and eof and sum(int(c[0]) for c in chunks) == req
    res[path] = {'requests': req, 'active': sum(int(c[1]) for c in chunks), 'already_irreducible': sum(int(c[2]) for c in chunks),
                 'chunks_reported': len(chunks), 'eof': eof, 'harness_errors': harness, 'valid': valid,
                 'error_diagnostics': len([e for e in errs if e[0] > end]),
                 'failing_declarations': sorted({f['decl'] for f in failing}), 'diagnostics': failing,
                 'seal_block_lines': [last := next(i for i, l in enumerate(sealed) if l.startswith('-- CP2 WHOLE-FILE SEAL')) + 1, end]}
    json.dump(res, open(out, 'w'), indent=1)
print('done', len(res))
