"""(bb1-sim, lead: copied unchanged from bb1-sim-statements.) (bb1-sim-statements, lead: copied unchanged from the bb1-machine delivery.)
sweepsum.py <repo> <results.jsonl> <base-sorries.txt> (fill bb1-machine, Claude lead): summary of a
runner.py sweep: rc, both error forms (`error:` and `error(`, G26-N1), sources bound to `git show HEAD`,
and the `sorry` warnings per module (from each module log) against the brief's base-sorries.txt."""
import sys, json, re, os, subprocess, hashlib
repo, res, bsf = sys.argv[1:4]
H = subprocess.run(['git', '-C', repo, 'rev-parse', 'HEAD'], capture_output=True, text=True).stdout.strip()
R = [json.loads(l) for l in open(res)]; M = [r for r in R if 'module' in r]
d = os.path.dirname(res); bound = 0; sor = {}
for r in M:
    b = subprocess.run(['git', '-C', repo, 'show', f'HEAD:{r["module"]}.lean'], capture_output=True).stdout
    bound += hashlib.sha256(b).hexdigest() == r['source_sha256']
    log = open(os.path.join(d, 'mods', r['module'].replace('/', '_') + '.log'), encoding='utf-8').read()
    for m in re.finditer(r"^(\S+\.lean):(\d+):\d+: warning: declaration uses 'sorry'", log, re.M):
        sor.setdefault(r['module'], []).append(int(m.group(2)))
print(f'head {H}; modules {len(M)}; rc!=0 {sum(r["rc"] != 0 for r in M)}; '
      f'errors (error: and error( forms) {sum(r["errors"] for r in M)}; error substrings {sum(r["error_substr"] for r in M)}; '
      f'sources bound to git show HEAD {bound}/{len(M)}; last record {R[-1]}')
print(f'sorry warnings {sum(map(len, sor.values()))} in {len(sor)} modules')
for k in sorted(sor): print(' ', k, len(sor[k]), sor[k])
print('--- base-sorries.txt'); print(open(bsf).read())
