"""Rule 10 whole-file seals for the gsw-core fill (python3 -I).

Adapted from the derand fill's audited harness (exchange inbox/fills/derand/evidence/verification/
tools/make_seals.py and run_seals.py, itself after Gate 10's archived harness): the install block is
copied verbatim except for its log prefix (GSWCORE instead of DERAND).

The probe is the source file with `import Lean` and the install block inserted right after its
last `import` line, so every imported TCSlib definition (not reducible, or a matcher) is made
`[local irreducible]` and dropped from the instance-unfolding set before the file's own
declarations elaborate. Variant A exempts `Complexity.PolyExpr.eval`; B seals it. The coe
variant also exempts exact projection-bodied `Coe`/`CoeFun` instances. coe-A is canonical.

usage:
  seal.py prepare OUTDIR LABEL SRC [--rev REV] [--variants A_coe,A_strict,B_coe,B_strict]
  seal.py run OUTDIR ROOT OLEANS     (runs every probe of OUTDIR/manifest.json, serially,
                                      under the host lock, with -DmaxErrors=0)
"""
import datetime, fcntl, json, os, re, resource, subprocess, sys, time
from pathlib import Path

TOOLS = Path(__file__).resolve().parent
INSTALL = (TOOLS / 'seal_install.lean.txt').read_text()
EOF = '\n\nrun_cmd do\n  let label := "LABEL"\n  Lean.logInfo m!"GSWCORE-EOF {label}"\n'
LOCK = '/home/user/gsw/.lean.lock'
ERR = re.compile(r'^\S+\.lean:(\d+):(\d+): error[:(].*$', re.M)


def prepare_one(src, label, mode, coe):
    lines = src.splitlines(keepends=True)
    last = max(i for i, line in enumerate(lines) if line.startswith('import '))
    block = INSTALL.replace('LABEL', label).replace('INCLUDEEVAL', str(mode == 'B').lower())
    block = block.replace('PROJECTIONCOES', str(coe).lower())
    head = ''.join(lines[:last + 1]) + 'import Lean\n' + block
    probe = head + ''.join(lines[last + 1:]) + EOF.replace('LABEL', label)
    mapping = [None] * head.count('\n') + list(range(last + 2, len(lines) + 1))
    mapping += [None] * (probe.count('\n') - len(mapping))
    return probe, mapping


def prepare(outdir, label, src_path, rev=None, variants=None):
    out = Path(outdir); out.mkdir(parents=True, exist_ok=True)
    if rev:
        src = subprocess.check_output(['git', 'show', f'{rev}:{src_path}'], text=True)
    else:
        src = Path(src_path).read_text()
    variants = variants or ['A_coe', 'A_strict', 'B_coe', 'B_strict']
    man_path = out / 'manifest.json'
    manifest = json.loads(man_path.read_text()) if man_path.exists() else []
    stem = Path(src_path).with_suffix('').as_posix().replace('/', '_')
    for v in variants:
        mode, kind = v.split('_')
        lab = f'{label}_{stem}_{v}'
        probe, mapping = prepare_one(src, lab, mode, kind == 'coe')
        dest = out / f'{stem}_{v}.lean'
        dest.write_text(probe)
        dest.with_suffix('.linemap.json').write_text(json.dumps(mapping) + '\n')
        manifest = [m for m in manifest if m['probe'] != str(dest)]
        manifest.append(dict(source=src_path, rev=rev or 'worktree', probe=str(dest), label=lab,
                             mode=mode, variant=kind))
    man_path.write_text(json.dumps(manifest, indent=2) + '\n')
    print(f'prepared {len(variants)} probes of {src_path} in {out}')


def run(outdir, root, oleans):
    out = Path(outdir).resolve(); root = Path(root).resolve()
    manifest = json.loads((out / 'manifest.json').read_text())
    lp = [oleans]
    lp += [str(d) for d in sorted((root / '.lake/packages').glob('*/.lake/build/lib/lean'))]
    env = dict(os.environ, LEAN_PATH=':'.join(lp),
               PATH=os.path.expanduser('~/.elan/bin') + ':' + os.environ['PATH'])
    scratch = out / '_olean'; scratch.mkdir(exist_ok=True)
    allok = True
    for item in manifest:
        probe = Path(item['probe']).resolve(); log = probe.with_suffix('.log')
        cmd = ['lean', '-DmaxErrors=0', os.path.relpath(probe, root), '-o', str(scratch / (probe.stem + '.olean'))]
        with open(LOCK, 'w') as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            start = datetime.datetime.now(datetime.timezone.utc).isoformat()
            t0 = time.monotonic()
            p = subprocess.run(cmd, cwd=root, env=env, stdout=subprocess.PIPE,
                               stderr=subprocess.STDOUT, text=True)
            secs = time.monotonic() - t0
            end = datetime.datetime.now(datetime.timezone.utc).isoformat()
        rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
        raw = (f'START {start}\nCOMMAND {cmd}\nLEAN_PATH {env["LEAN_PATH"]}\n' + p.stdout +
               f'END {end}\nEXIT {p.returncode}\nMAX_RSS_KIB_SO_FAR {rss}\n')
        log.write_text(raw)
        mapping = json.loads(probe.with_suffix('.linemap.json').read_text())
        errors = []
        for m in ERR.finditer(p.stdout):
            ln = int(m[1])
            errors.append(dict(probe_line=ln,
                               source_line=mapping[ln - 1] if ln <= len(mapping) else None,
                               diagnostic=m[0]))
        inst = re.findall(r'GSWCORE-INSTALL ' + re.escape(item['label']) + r' (requested=\d+ '
                          r'active=\d+ already=\d+ excluded=\d+)', p.stdout)
        eof = p.stdout.count('GSWCORE-EOF ' + item['label'])
        harness = len(inst) == 1 and eof == 1 and all(e['source_line'] for e in errors)
        sorries = len(re.findall(r"declaration uses 'sorry'", p.stdout))
        row = dict(item, start=start, end=end, seconds=round(secs, 1), exit=p.returncode,
                   error_count=len(errors), errors=errors, install=inst[0] if inst else None,
                   eof=eof, harness_valid=harness, sorry_warnings=sorries)
        with (out / 'results.jsonl').open('a') as f:
            f.write(json.dumps(row) + '\n')
        allok &= harness
        print(f'{probe.name}: exit={p.returncode} errors={len(errors)} harness={harness} '
              f'{inst[0] if inst else "NO-INSTALL"} sorry={sorries}')
        for e in errors:
            print(f'   src line {e["source_line"]}: {e["diagnostic"][:220]}')
    sys.exit(0 if allok else 2)


if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == 'prepare':
        rev = a[a.index('--rev') + 1] if '--rev' in a else None
        var = a[a.index('--variants') + 1].split(',') if '--variants' in a else None
        prepare(a[1], a[2], a[3], rev, var)
    elif a[0] == 'run':
        run(a[1], a[2], a[3])
