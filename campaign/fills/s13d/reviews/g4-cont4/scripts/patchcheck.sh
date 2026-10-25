#!/usr/bin/env bash
set -u
R="$1"; D="$2"; G="$3"; F="$4"; B="$5"; H="$6"
T=$R/patchapply; rm -rf "$T"; mkdir -p "$T/$(dirname $F)"
git -C "$G" show "$B:$F" > "$T/$F"
n=0
for p in "$D"/patches/*.patch; do
  n=$((n+1))
  files=$(grep -E '^diff --git ' "$p" | awk '{print $3}' | sort -u | tr '\n' ' ')
  [ "$files" = "a/$F " ] || echo "PATCH $n touches: $files"
  (cd "$T" && git apply --whitespace=nowarn "$p") || { echo "APPLY FAILED $n $p"; exit 1; }
done
echo "patches applied: $n"
cmp "$T/$F" "$D/source/$F" && echo "result == delivered source (byte-for-byte)"
echo "result blob: $(git hash-object "$T/$F")"
echo "== commits base..head (oldest first)"
git -C "$G" log --reverse --format='%H %an <%ae> %aI | %s' "$B..$H" | nl
echo "count: $(git -C "$G" rev-list --count "$B..$H")"
echo "== linear? merges: $(git -C "$G" rev-list --merges --count "$B..$H")"
echo "== first parent of first commit: $(git -C "$G" log --reverse --format=%P "$B..$H" | head -1)"
echo "== files touched per commit"
for c in $(git -C "$G" rev-list --reverse "$B..$H"); do
  fl=$(git -C "$G" diff-tree --no-commit-id --name-only -r "$c" | tr '\n' ' ')
  st=$(git -C "$G" diff-tree --no-commit-id --numstat -r "$c" | awk '{printf "+%s/-%s", $1, $2}')
  echo "${c:0:8} $st $fl"
done
echo "== format-patch comparison"
FP=$R/out/fp; rm -rf "$FP"; mkdir -p "$FP"
git -C "$G" format-patch -q -o "$FP" "$B..$H"
i=0
for p in "$D"/patches/*.patch; do
  i=$((i+1)); q=$(ls "$FP" | sed -n "${i}p")
  if diff <(grep -v -E '^(-- |[0-9]+\.[0-9]+\.[0-9]+.*$)' "$p" | sed '$d') <(grep -v -E '^(-- |[0-9]+\.[0-9]+\.[0-9]+.*$)' "$FP/$q" | sed '$d') >/dev/null; then :; else
    if diff <(sed -e '/^-- $/,$d' "$p") <(sed -e '/^-- $/,$d' "$FP/$q") > /dev/null; then :; else echo "DIFFERS: $(basename $p) vs $q"; fi
  fi
  [ "$(basename "$p")" = "$q" ] || echo "NAME: $(basename $p) vs $q"
done
echo "format-patch compared: $i (up to the git-version trailer)"
