#!/bin/bash
# Wait until fewer than three Lean processes are active, then run one command.
# This does not interrupt other sessions or claim a lock they do not honor.
set -eu
while [ -f .lake/dl-crh-audit-preparation-hold ]; do
  date -u '+WAIT audit preparation at %Y-%m-%dT%H:%M:%SZ'
  sleep 5
done
while ps -axo pid=,comm= | awk '$NF ~ /(^|\/)lean$/ { count++ } END { exit !(count >= 3) }'; do
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
