#!/usr/bin/env bash
# usage: chk.sh <module> <logfile>  — one module via scripts/lean_check_tree.sh, timed, max RSS
cd /home/user/fill
export PATH=$HOME/.elan/bin:$PATH
m="$1"; log="$2"
{ echo "== $m start $(date -u +%FT%TZ)"
  python3 -I -c '
import resource, subprocess, sys, time
t=time.time(); s=subprocess.call(["bash","scripts/lean_check_tree.sh",sys.argv[1]])
print(f"elapsed {time.time()-t:.1f}s; max RSS of children {resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss/1024:.0f} MiB")
sys.exit(s)' "$m"; s=$?
  echo "== $m end $(date -u +%FT%TZ) status $s"; } >>"$log" 2>&1
tail -n 60 "$log" | grep -E "^== |elapsed|FAIL|error" | tail -5
