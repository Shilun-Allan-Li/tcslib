#!/usr/bin/env bash
# Usage: bash screen_run.sh <root> <commit label> <population file> <out prefix>
root="$1"; label="$2"; pop="$3"; out="$4"
files=(); while IFS= read -r l; do [[ "$l" == \#* || -z "$l" ]] || files+=("$l"); done < "$pop"
echo "root $root commit $label files ${#files[@]} $(date)" > "$out.status"
( cd "$root" && /usr/bin/time -l python3 -I scripts/copy-text-screen-v3.py . "${files[@]}" ) > "$out.txt" 2> "$out.time"
echo "exit $?" >> "$out.status"
