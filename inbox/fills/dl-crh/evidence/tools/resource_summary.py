#!/usr/bin/env python3
"""Summarize native macOS counters retained by preflight.sh.

The native proxy is identified explicitly; it is not Linux MemAvailable.
"""
from pathlib import Path
import re

raw = Path("evidence/logs/resume-1/preflight.log").read_text()
fields = {name: int(value) for name, value in re.findall(
    r"^(Pages [^:]+|Anonymous pages):\s+(\d+)\.", raw, re.M)}
physical = int(re.search(r"hw.memsize: (\d+)", raw)[1])
page_size = int(re.search(r"page size of (\d+) bytes", raw)[1])
used_pages = sum(fields[key] for key in
                 ("Anonymous pages", "Pages wired down", "Pages occupied by compressor"))
used = used_pages * page_size
print("physical_bytes", physical)
print("page_size", page_size)
print("native_noncache_used_proxy_bytes", used)
print("native_headroom_proxy_bytes", physical - used)
print("native_proxy_at_least_4_GiB", physical - used >= 4 * 1024**3)
print("Linux cgroup/MemAvailable counters unavailable; native proxy, not a claimed exact replacement")
