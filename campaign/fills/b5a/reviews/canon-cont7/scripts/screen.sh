#!/usr/bin/env bash
# Disabled after the maintainer's session restart (coordinator: "do not start another screen").
# The after-screen already running keeps reading its own copy of the original script (kept as
# screen.sh.as-run); any later invocation of this path only records that it was skipped.
echo "skipped (screen.sh disabled) $(date -u +%FT%TZ) args: $*" >> "${2:-/dev/null}.status"
exit 0
