#!/usr/bin/env bash
# Called only inside lean-slot.sh: snapshot the source after acquiring the host slot.
set -u
module="$1"
snapshot="$2"
cp "$module.lean" "$snapshot"
bash scripts/lean_check_tree.sh "$module"
