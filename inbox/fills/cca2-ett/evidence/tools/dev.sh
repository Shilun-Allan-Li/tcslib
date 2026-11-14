#!/usr/bin/env bash
# Dev check of one module: fresh log, print status and errors/warnings.
m="$1"; log=/workspace/ett-work/$(echo "$m" | tr / _).log
rm -f "$log"
/workspace/ett-tools/check.sh "$m" "$log"
grep -E "status=|time:" "$log"
grep -E "error|warning" "$log" | grep -v "^Note" | head -${2:-40}
