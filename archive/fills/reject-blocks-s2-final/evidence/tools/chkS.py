#!/usr/bin/env python3
# Run scripts/lean_check_tree.sh on one module; log start/end, wall time, max RSS of children.
import subprocess, sys, time, resource, datetime, os
mod = sys.argv[1]
t0 = time.time()
print(f"== {mod} start {datetime.datetime.utcnow().strftime('%H:%M:%S')}", flush=True)
p = subprocess.run(["bash", "scripts/lean_check_tree.sh", mod], cwd="/workspace/tcslib-fill", env=dict(os.environ, TCSLIB_OLEANS="/workspace/s2-oleans"))
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"== {mod} end {datetime.datetime.utcnow().strftime('%H:%M:%S')} rc={p.returncode} wall={time.time()-t0:.1f}s maxrss={ru.ru_maxrss//1024}MiB", flush=True)
ol=f"/workspace/s2-oleans/{mod}.olean"
fresh = os.path.exists(ol) and os.path.getsize(ol)>0 and os.path.getmtime(ol)>=t0
print(f"== {mod} olean fresh-nonempty={fresh}", flush=True)
sys.exit(p.returncode if fresh or p.returncode else 1)
