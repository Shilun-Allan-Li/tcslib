#!/usr/bin/env bash
# Compare a census with base-sorries.txt (whose Complexity rows omit the TCSlib/Complexity/ prefix).
diff <(sed 's|^TCSlib/Complexity/||' "$1" | sort) <(sed 's|^TCSlib/Complexity/||' /workspace/canon-pack/base-sorries.txt | sort) && echo "CENSUS IDENTICAL TO base-sorries.txt"
echo "diff exit=$?"
