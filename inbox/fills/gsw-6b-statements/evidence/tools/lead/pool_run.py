"""[gsw-6b-statements copy of gsw-6a-fills evidence/tools/lead/pool_run.py; changes: POOL default /home/user/pool.] pool_run.py <label> <logfile> -- <cmd...> (gsw-6a-fills, new): run one Lean command (a module check through
scripts/lean_check_tree.sh, a probe, a seal) under one slot of the shared pool (poollib.py), output to <logfile>;
prints rc, max RSS and seconds; exits with the command's rc. Use this for every Lean process of every agent."""
import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poollib
label, logf = sys.argv[1], sys.argv[2]
cmd = sys.argv[sys.argv.index('--') + 1:]
env = dict(os.environ); env['PATH'] = os.path.expanduser('~/.elan/bin') + ':' + env.get('PATH', '')
os.makedirs(os.path.dirname(os.path.abspath(logf)), exist_ok=True)
with open(logf, 'wb') as out:
    rc, rss, sec = poollib.run(label, cmd, env=env, stdout=out)
print(f'rc={rc}\tmaxrss_kb={rss}\tseconds={sec}\tlog={logf}')
sys.exit(rc)
