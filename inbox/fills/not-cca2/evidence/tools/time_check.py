"""Check one module through scripts/lean_check_tree.sh; log UTC start/end, elapsed, max child RSS."""
import datetime
import resource
import subprocess
import sys
import time

print('START', datetime.datetime.now(datetime.timezone.utc).isoformat(), flush=True)
print('MODULE', sys.argv[1], flush=True)
start = time.monotonic()
result = subprocess.run(['bash', 'scripts/lean_check_tree.sh', sys.argv[1]])
usage = resource.getrusage(resource.RUSAGE_CHILDREN)
print('END', datetime.datetime.now(datetime.timezone.utc).isoformat())
print('Elapsed seconds: %.1f' % (time.monotonic() - start))
print('Maximum child RSS (KiB):', usage.ru_maxrss)
print('EXIT', result.returncode)
sys.exit(result.returncode)
