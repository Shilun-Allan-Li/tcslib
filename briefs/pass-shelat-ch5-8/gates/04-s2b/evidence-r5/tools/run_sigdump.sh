#!/usr/bin/env bash
# run_sigdump.sh <source-root> <olean-tree> <files.txt> <out.tsv>: elaborated-signature dump of every
# module of <files.txt> present at that source root (no .olean written).
set -u
ROOT="$1"; OL="$2"; FILES="$3"; OUT="$4"
TOOLS="$(cd "$(dirname "$0")" && pwd)"
export PATH="$HOME/.elan/bin:$PATH"
LP="$OL"; for d in "$ROOT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"
F="$OUT.lean"
{ while read -r f; do [ -n "$f" ] && [ -f "$ROOT/$f" ] && echo "import $(echo ${f%.lean} | tr / .)"; done < "$FILES"
  echo; echo "open Lean in"
  printf 'def targetMods : Array Name := #['
  first=1; while read -r f; do [ -n "$f" ] && [ -f "$ROOT/$f" ] || continue; [ $first = 1 ] || printf ', '; printf '`%s' "$(echo ${f%.lean} | tr / .)"; first=0; done < "$FILES"
  echo ']'; echo "def outFile : System.FilePath := \"$OUT\""; echo; cat "$TOOLS/sigdump_body.lean"; } > "$F"
cd "$ROOT" && lean "$F" > "$OUT.log" 2>&1; rc=$?
echo "sigdump rc=$rc $(wc -l < "$OUT" 2>/dev/null) constants"; grep -m5 error "$OUT.log"
exit $rc
