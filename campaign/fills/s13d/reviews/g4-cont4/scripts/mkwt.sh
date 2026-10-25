#!/usr/bin/env bash
set -u
R="$1"; G=/Users/seyoonr/phd_experiments/tcslib
while read -r name rev; do
  [ -z "$name" ] && continue
  p="$R/$name"
  if [ -e "$p" ]; then echo "EXISTS $p"; continue; fi
  git -C "$G" worktree add --detach "$p" "$rev" >/dev/null 2>&1 || { echo "FAILED $name"; continue; }
  h=$(git -C "$p" rev-parse HEAD); echo "added $name at $h (wanted $rev)"; [ "$h" = "$rev" ] || echo "MISMATCH $name"
  if [ -e "$p/.lake/packages" ]; then echo "PACKAGES EXIST in $p"; else mkdir -p "$p/.lake" && ln -s "$G/.lake/packages" "$p/.lake/packages" && echo "linked $p/.lake/packages"; fi
done
