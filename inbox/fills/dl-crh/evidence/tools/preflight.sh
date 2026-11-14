#!/bin/bash
# Read-only native host diagnostics. Does not invoke Lean or Lake.
set -u
WORKTREE="$1"
date -u '+UTC %Y-%m-%dT%H:%M:%SZ'
uname -a
printf '\nRequested Linux counters (unavailable on this macOS host):\n'
command -v nproc && nproc
for f in /sys/fs/cgroup/memory.max /sys/fs/cgroup/memory.current /sys/fs/cgroup/memory.events /sys/fs/cgroup/memory.stat /proc/meminfo; do
  if [ -r "$f" ]; then cat "$f"; else printf 'UNAVAILABLE %s\n' "$f"; fi
done
printf '\nmacOS native counters:\n'
sysctl hw.memsize hw.ncpu
vm_stat
memory_pressure -Q
printf '\nDisk, 1024-byte blocks (multiply Available by 1024 for bytes):\n'
df -k "$WORKTREE" /private/tmp
printf '\nFilesystem types:\n'
mount
printf '\nExisting Lean/Lake processes; none will be interrupted:\n'
ps -axo pid,command | rg '(^|/)(lean|lake|leantar)( |$)' || true
printf '\nNo Lean/Lake or cache work was started by this fill.\n'
printf 'This is a native diagnostic, not a certification of Linux MemAvailable.\n'
