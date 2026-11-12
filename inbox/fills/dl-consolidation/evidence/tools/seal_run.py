#!/usr/bin/env python3
"""Run whole-file closure seals, one Lean process at a time.

Usage: seal_run.py <worktree> <tag> <log.jsonl> [--eval-open] <src.lean>...

For each source file, writes the sealed copy `lean_proof/dlc/seal/<tag>/<Name>.lean` in the
worktree (seal_gen.py), checks it with scripts/lean_check_tree.sh (time and max RSS recorded),
and appends one JSON row: file, copy, status, number of errors, the declarations at the error
lines, the DLC-SEAL counts line, the copy's and the source's sha256."""
import sys, os, re, json, subprocess, hashlib, time

wt, tag, logp = sys.argv[1], sys.argv[2], sys.argv[3]
rest = sys.argv[4:]
eval_open = '--eval-open' in rest
srcs = [a for a in rest if not a.startswith('--')]
DECL = re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |unsafe |partial )*'
                  r'(theorem|lemma|def|abbrev|instance|structure|inductive|example|opaque)\s+([^\s:(\[{]*)')

def decl_at(lines, ln):
    for i in range(min(ln, len(lines)) - 1, -1, -1):
        m = DECL.match(lines[i])
        if m:
            return m.group(2) or m.group(1)
    return '?'

def sha(p):
    return hashlib.sha256(open(p, 'rb').read()).hexdigest()

for src in srcs:
    name = src[:-5].replace('TCSlib/Cryptography/', '').replace('/', '_')
    out = f'lean_proof/dlc/seal/{tag}/{name}'
    subprocess.run(['python3', '/workspace/dlc-tools/seal_gen.py', wt, src, out] +
                   (['--eval-open'] if eval_open else []), check=True, capture_output=True)
    t0 = time.time()
    r = subprocess.run(['/usr/bin/time', '-f', 'time: elapsed=%e s, maxrss=%M KiB, exit=%x',
                        'bash', 'scripts/lean_check_tree.sh', out], cwd=wt, capture_output=True, text=True)
    txt = r.stdout + r.stderr
    copy_lines = open(os.path.join(wt, out + '.lean')).read().split('\n')
    errs = []
    for m in re.finditer(r'^' + re.escape(out) + r'\.lean:(\d+):(\d+): error', txt, re.M):
        ln = int(m.group(1))
        errs.append((ln, decl_at(copy_lines, ln)))
    counts = re.search(r'DLC-SEAL [^\n]*sealed=[^\n]*', txt)
    tm = re.search(r'time: [^\n]*', txt)
    row = {'file': src, 'copy': out + '.lean', 'variant': 'eval-open' if eval_open else 'eval-sealed',
           'status': r.returncode, 'errors': len(errs),
           'error_decls': sorted(set(d for _, d in errs)), 'error_lines': [l for l, _ in errs],
           'seal': counts.group(0) if counts else None, 'time': tm.group(0) if tm else None,
           'source_sha256': sha(os.path.join(wt, src)), 'copy_sha256': sha(os.path.join(wt, out + '.lean'))}
    with open(logp, 'a') as f:
        f.write(json.dumps(row, ensure_ascii=False) + '\n')
    with open(logp.replace('.jsonl', '.out'), 'a') as f:
        f.write(f'===== {src} [{row["variant"]}]\n' + txt + '\n')
    print(src, row['status'], row['errors'], row['error_decls'][:5], flush=True)
