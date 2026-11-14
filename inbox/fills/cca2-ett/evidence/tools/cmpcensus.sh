#!/usr/bin/env bash
diff <(sed 's|^TCSlib/Complexity/||' "$1" | sort) <(sed 's|^TCSlib/Complexity/||' /workspace/ett-pack/base-sorries.txt | sort) && echo "CENSUS IDENTICAL TO base-sorries.txt"
