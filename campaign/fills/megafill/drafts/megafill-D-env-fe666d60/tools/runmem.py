"""runmem.py LABEL -- CMD...: run CMD, pass its output through, then print one line
`MEM LABEL start=<UTC> end=<UTC> secs=<s> exit=<n> maxrss_kib=<k>`.
The peak resident set is getrusage(RUSAGE_CHILDREN).ru_maxrss (KiB on Linux): the largest
descendant that was waited for (here `lean`, waited for by `bash`)."""
import datetime, resource, subprocess, sys, time

label = sys.argv[1]
assert sys.argv[2] == '--'
cmd = sys.argv[3:]
start = datetime.datetime.now(datetime.timezone.utc)
t0 = time.monotonic()
rc = subprocess.call(cmd)
secs = time.monotonic() - t0
end = datetime.datetime.now(datetime.timezone.utc)
rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
fmt = '%Y-%m-%dT%H:%M:%SZ'
print(f'MEM {label} start={start.strftime(fmt)} end={end.strftime(fmt)} secs={secs:.1f} '
      f'exit={rc} maxrss_kib={rss}', flush=True)
sys.exit(rc)
