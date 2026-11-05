#!/usr/bin/env bash
# Gate 89 round 4: the binary-length sweep. Every line of TCSlib/**/*.lean at <rev> that uses a
# Mathlib or TCSlib fact relating Nat.size, the binary length |Nat.bits n| and Nat.log:
# Nat.size_le, Nat.size_le_size, Nat.lt_size, Nat.lt_size_self, Nat.size_eq_bits_len,
# Nat.lt_pow_succ_log_self, LogProg.length_bits_le(_log|_self), logSpace_le_size_succ,
# size_le_logSpace; each with the enclosing declaration.
# Usage: bash bitsweep.sh <repo worktree> <rev> <out file>
# Portable matching (round 5): no `\b`; a name ends at a non-identifier character or the line's end.
set -u
cd "$1" || exit 1
PAT='Nat\.size_le([^_[:alnum:]]|$)|size_le\.m|Nat\.size_le\]|size_le_size|lt_pow_succ_log_self|length_bits_le|size_eq_bits_len|Nat\.lt_size([^_[:alnum:]]|$)|lt_size\.m|lt_size_self|size_le_logSpace|logSpace_le_size'
{
  echo "# rev $(git rev-parse "$2"); pattern: $PAT"
  git grep -n -E "$PAT" "$2" -- 'TCSlib/*.lean' | sed "s|^$2:||" | while IFS=: read -r f n rest; do
    d=$(git show "$2:$f" | awk -v N="$n" 'NR<=N && /^(@\[[^]]*\] *)?(private |protected |noncomputable )*(theorem|lemma|def|abbrev) /{l=$0} END{print l}' \
        | sed -E 's/^(@\[[^]]*\] *)?(private |protected |noncomputable )*(theorem|lemma|def|abbrev) ([^ ]+).*/\4/')
    printf '%s:%s\t%s\t%s\n' "$f" "$n" "${d:-?}" "$(echo "$rest" | sed 's/^ *//' | cut -c1-120)"
  done
} > "$3"
