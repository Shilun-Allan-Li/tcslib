#!/usr/bin/env bash
# usage: chk.sh <module> <logfile-append>
export PATH=$HOME/.elan/bin:$PATH
cd /home/user/work
m="$1"; log="$2"
echo "=== $m start $(date -u +%FT%TZ)" >> "$log"
python3 -c '
import subprocess,sys,resource,time
t=time.time()
r=subprocess.run(["bash","scripts/lean_check_tree.sh",sys.argv[1]])
print(f"maxrss_kb={resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss} elapsed={time.time()-t:.1f}s",flush=True)
sys.exit(r.returncode)' "$m" >> "$log" 2>&1
st=$?
echo "=== $m end $(date -u +%FT%TZ) exit=$st" >> "$log"
exit $st
