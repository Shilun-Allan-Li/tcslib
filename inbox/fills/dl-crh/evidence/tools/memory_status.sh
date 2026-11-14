#!/bin/bash
# Read-only counters during an already-running check; no Lean or Lake is launched.
set -u
date -u '+UTC %Y-%m-%dT%H:%M:%SZ'
sysctl hw.memsize hw.ncpu
vm_stat
memory_pressure -Q
ps -axo pid,comm | awk '$NF ~ /\/(lean|lake)$/ {print}'
