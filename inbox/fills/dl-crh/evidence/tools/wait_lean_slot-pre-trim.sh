#!/bin/bash
# Wait until fewer than three Lean processes are active, then run one command.
# This does not interrupt other sessions or claim a lock they do not honor.
set -eu
while ps -axo comm= | awk -F/ '$NF == "lean" { count++ } END { exit !(count >= 3) }'; do
  date -u '+WAIT existing Lean/Lake process at %Y-%m-%dT%H:%M:%SZ'
  sleep 5
done
date -u '+START %Y-%m-%dT%H:%M:%SZ'
set +e
/usr/bin/time -l "$@"
status=$?
date -u '+END %Y-%m-%dT%H:%M:%SZ'
printf 'EXIT %s\n' "$status"
exit "$status"
