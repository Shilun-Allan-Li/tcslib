"""check.py <worktree> <module> <log> (gsw-6a-fills; the statement job's check.py with its host-wide lock replaced
by one slot of the shared Lean pool): compile <module> with `bash scripts/lean_check_tree.sh` (olean into
$TCSLIB_OLEANS or <worktree>/.lake/tcslib-check-oleans), full output to <log>, a summary line to <log>.summary."""
import sys, os, re, subprocess
sys.path.insert(0, '/home/user/w6/tools')
import poollib
wt, mod, log = sys.argv[1:4]
env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
env.setdefault('TCSLIB_OLEANS', os.path.join(wt, '.lake/tcslib-check-oleans'))
os.makedirs(os.path.dirname(os.path.abspath(log)), exist_ok=True)
with open(log, 'wb') as out:
    rc, rss, sec = poollib.run(f'check:{mod}', ['bash', 'scripts/lean_check_tree.sh', mod], cwd=wt, env=env, stdout=out)
txt = open(log, encoding='utf-8', errors='replace').read()
errs = len(re.findall(r'^\S+\.lean:\d+:\d+: error[:(]', txt, re.M))
line = f"{mod}\trc={rc}\terrors={errs}\tsorry={txt.count(chr(39).join(['declaration uses ', 'sorry', '']))}\tseconds={sec}\tmaxrss_kb={rss}"
open(log + '.summary', 'w').write(line + '\n'); print(line)
sys.exit(rc)
