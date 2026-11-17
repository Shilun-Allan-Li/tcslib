"""hold_pool.py <logfile> -- <cmd...> (gsw-6b-statements, new): run a command while holding every slot
of the shared Lean pool (blocking flock on slot0..slot7, so running Lean processes finish first and
no new one starts), for `lake exe cache get`, which must run alone (addendum: "The cache tool runs
alone"). Logs HOLD/UNHOLD to the pool log."""
import sys, os, fcntl, subprocess
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import poollib
logf = sys.argv[1]; cmd = sys.argv[sys.argv.index('--') + 1:]
fds = []
for i in range(8):
    fd = os.open(os.path.join(poollib.POOL, f'slot{i}'), os.O_CREAT | os.O_RDWR)
    fcntl.flock(fd, fcntl.LOCK_EX); fds.append(fd)
poollib.log(f'HOLD\tall-slots\tmemavail={poollib.memavail()}\t{" ".join(cmd)[:120]}')
with open(logf, 'wb') as out:
    rc = subprocess.run(cmd, stdout=out, stderr=subprocess.STDOUT).returncode
poollib.log(f'UNHOLD\tall-slots\trc={rc}\tmemavail={poollib.memavail()}')
for fd in fds: fcntl.flock(fd, fcntl.LOCK_UN); os.close(fd)
print(f'rc={rc}'); sys.exit(rc)
