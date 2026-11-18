# Minimal /usr/bin/time -v substitute: run argv, then print max RSS of the child tree.
import sys, subprocess, resource, time
t0 = time.time()
rc = subprocess.call(sys.argv[1:])
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"\tElapsed (wall clock) time (s): {time.time()-t0:.1f}")
print(f"\tMaximum resident set size (kbytes): {ru.ru_maxrss}")
print(f"\tExit status: {rc}")
sys.exit(rc)
