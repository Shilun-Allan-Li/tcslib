#!/usr/bin/env bash
# overlap_search.sh [<log>] -- overlap (near-relative) searches for fill ef-r23-regev.
# ORIGIN (tools-agent, sub-agent of fill ef-r23-regev, 2026-11-18): modelled on the search log of fill bb1-machine
# (/home/user/ef-r23/tools/bb1m-evidence/overlap/search.log: every command verbatim, its hit count and its hits).
# Adaptations: the searches are the ef-r23 brief's list (general-modulus vector addition / subset sums / mulVec over
# ZMod on encodings, BinArith.mod composed with BinArith.add, NUPPT/RealizesOn in Encryption/*/Regev/, GSW analogues
# on PR #377, worst-message advice in PrivateKey/FromPRG.lean, coin-transport lemmas, modContext-like context
# helpers); trees: the base 5ed465f6 (`git grep`, TCSlib/), PR #377 head 7563734a (`git grep`, TCSlib/), Mathlib
# sources (plain `grep -rn`, read-only). Read-only; no Lean. Output lines per hit are capped at $CAP (default 60)
# per search; the hit count is always the full count.
set -u
R=/home/user/ef-r23/repo
BASE=5ed465f62e4ae0f93ded1a1ba49e807591b589eb
P377=7563734a8badba842223e0687c719b3b4692e9d2
ML=$R/.lake/packages/mathlib/Mathlib
LOG=${1:-/home/user/ef-r23/evidence/subagents/tools-agent/overlap/search.log}
CAP=${CAP:-60}
mkdir -p "$(dirname "$LOG")"; : > "$LOG"
log() { printf '%s\n' "$*" >> "$LOG"; }
# run <tag> <command...>: log the command, the hit count and the first $CAP hits
run() {
  local tag=$1; shift
  local out; out=$("$@" 2>&1); local rc=$?
  local n; n=$(printf '%s' "$out" | grep -c . )
  log "### [$tag] \$ $(printf '%q ' "$@")"
  log "# exit $rc, hits $n"
  printf '%s\n' "$out" | head -n "$CAP" >> "$LOG"
  [ "$n" -gt "$CAP" ] && log "# ... ($((n - CAP)) more)"
  log ""
  printf '%-34s %5s hits  %s\n' "$tag" "$n" "$(printf '%q ' "$@" | cut -c1-150)"
}
log "# overlap_search.sh run $(date -u +%FT%TZ); repo $R; base $BASE; PR377 $P377; Mathlib $ML"
log "# mathlib rev: $(git -C "$R/.lake/packages/mathlib" rev-parse HEAD 2>/dev/null)"
log ""
for T in "base:$BASE" "pr377:$P377"; do
  tag=${T%%:*}; rev=${T#*:}
  # 1. general-modulus arithmetic on encodings
  run "$tag/encodeVector-defs"     git -C "$R" grep -n -E '(def|theorem|lemma) +(encodeVector|encodeMatrix)\b' "$rev" -- TCSlib
  run "$tag/vecAdd"                git -C "$R" grep -n -E '\bvecAdd[A-Za-z_]*' "$rev" -- TCSlib
  run "$tag/subsetSum"             git -C "$R" grep -n -E '\bsubsetSum[A-Za-z_]*' "$rev" -- TCSlib
  run "$tag/addMod|modAdd"         git -C "$R" grep -n -E '\b(addMod|modAdd|addModQ|modAddWords)[A-Za-z_]*' "$rev" -- TCSlib
  run "$tag/mulVec-on-encodings"   git -C "$R" grep -n -E 'mulVec' "$rev" -- TCSlib/Cryptography/Encoding TCSlib/Cryptography/LWE TCSlib/Cryptography/Encryption/Symmetric/Regev TCSlib/Cryptography/Encryption/PublicKey/Regev
  run "$tag/percent-q"             git -C "$R" grep -n -E '% *q\b' "$rev" -- TCSlib/Cryptography/Encoding TCSlib/Complexity/ClassP/BinaryArith TCSlib/Cryptography/LWE
  run "$tag/BinArith.mod-defs"     git -C "$R" grep -n -E '(def|theorem|lemma) +(mod|polyTimeComputable_mod|mod_eq|mod_pairEncode)[A-Za-z_]*\b' "$rev" -- TCSlib/Complexity/ClassP/BinaryArith
  run "$tag/BinArith.mod-uses"     git -C "$R" grep -n -E 'BinArith\.mod\b' "$rev" -- TCSlib
  run "$tag/mod-of-add"            git -C "$R" grep -n -E 'BinArith\.mod.*BinArith\.add|BinArith\.add.*BinArith\.mod' "$rev" -- TCSlib
  run "$tag/mod-near-add(-A3)"     git -C "$R" grep -n -A3 -E 'BinArith\.mod\b' "$rev" -- TCSlib
  run "$tag/dyadic-loops"          git -C "$R" grep -n -E '(def|theorem) +[A-Za-z_]*(dot|Dot|mulVecWords|addWords|AddWords|forLoop)[A-Za-z_]*' "$rev" -- TCSlib/Cryptography/Encoding
  # 2. NUPPT / RealizesOn in Encryption/*/Regev/
  run "$tag/NUPPT|RealizesOn-Regev" git -C "$R" grep -n -E 'NUPPT|RealizesOn' "$rev" -- 'TCSlib/Cryptography/Encryption/*/Regev/*' 'TCSlib/Cryptography/Encryption/*/Regev.lean'
  # 3. context helpers
  run "$tag/modContext-like"       git -C "$R" grep -n -E '\b[a-z][A-Za-z]*(Context|Ctx|ctxWord|modulusWord|modulusNumeral)\b *(\(|:)' "$rev" -- TCSlib/Cryptography/Encoding TCSlib/Cryptography/LWE TCSlib/Complexity/ClassP/BinaryArith
  run "$tag/natToList-modulus"     git -C "$R" grep -n -E 'natToList \(?[a-zA-Z]+ *\+ *1\)? +[a-zA-Z.]*(q|modulus)\b' "$rev" -- TCSlib
  # 4. worst-message advice pattern
  run "$tag/FromPRG-advice"        git -C "$R" grep -n -E 'exists_max_image|exists_withAdvice|withAdvice|Finset.exists_max' "$rev" -- TCSlib/Cryptography/Encryption/PrivateKey/FromPRG.lean
  run "$tag/exists_max_image-all"  git -C "$R" grep -n -E 'exists_max_image' "$rev" -- TCSlib/Cryptography
  run "$tag/exists_withAdvice-all" git -C "$R" grep -n -E 'exists_withAdvice|withAdvice_' "$rev" -- TCSlib
  # 5. coin transport
  run "$tag/coin-transport"        git -C "$R" grep -n -E 'acceptProb_coins_equiv|acceptProb_coins_fst|acceptProb_distinguisherL_congr|coinsCongr' "$rev" -- TCSlib
  run "$tag/Fin.append-coins"      git -C "$R" grep -n -E 'Fin\.append.*[Cc]oins|[Cc]oins.*Fin\.append' "$rev" -- TCSlib
  run "$tag/finSumFinEquiv-coins"  git -C "$R" grep -n -E 'finSumFinEquiv.*[Cc]oins|[Cc]oins.*finSumFinEquiv' "$rev" -- TCSlib
  # 6. realization entry points used by the new files
  run "$tag/exists_realizesOn"     git -C "$R" grep -n -E '(theorem|lemma) +[A-Za-z_.]*exists_realizesOn[A-Za-z_]*' "$rev" -- TCSlib
  run "$tag/distinguisherL_eq-RealizesOn" git -C "$R" grep -n -E '(theorem|lemma) +[A-Za-z_.]*RealizesOn\.[A-Za-z_]*' "$rev" -- TCSlib
  # 7. existing single-message security / DLWE consumers
  run "$tag/singleMessageSecure"   git -C "$R" grep -n -E 'singleMessageSecure|SingleMessageSecure' "$rev" -- TCSlib/Cryptography/Encryption
  run "$tag/DLWEAssumption-uses"   git -C "$R" grep -n -E 'DLWEAssumption' "$rev" -- TCSlib
  run "$tag/shift-defs"            git -C "$R" grep -n -E '(def|theorem) +(shift|shift_[A-Za-z_]*|[a-z]*Shift[A-Za-z_]*)\b' "$rev" -- TCSlib/Cryptography/Encryption TCSlib/Cryptography/LWE
done
# GSW analogues on #377 (and their absence at base)
for T in "base:$BASE" "pr377:$P377"; do
  tag=${T%%:*}; rev=${T#*:}
  run "$tag/GSW-encodeView"        git -C "$R" grep -n -E 'encodeView' "$rev" -- TCSlib
  run "$tag/GSW-ReductionEfficient" git -C "$R" grep -n -E 'ReductionEfficient' "$rev" -- TCSlib
  run "$tag/GSW-reductionMachine"  git -C "$R" grep -n -E 'reductionMachine' "$rev" -- TCSlib
  run "$tag/GSW-reduction-defs"    git -C "$R" grep -n -E '(def|theorem|structure) +[A-Za-z_.]*([Rr]eduction|encodeView)[A-Za-z_]*' "$rev" -- TCSlib/Cryptography/AdvancedEncryption/Homomorphic
  run "$tag/GSW-files"             git -C "$R" ls-tree -r --name-only "$rev" -- TCSlib/Cryptography/AdvancedEncryption/Homomorphic/GSW
done
run "diff/base..pr377-files"       git -C "$R" diff --name-status "$BASE" "$P377" -- TCSlib
# Mathlib (plain grep, read-only)
run "mathlib/ZMod-mulVec"          grep -rnE 'theorem [A-Za-z_.]*mulVec[A-Za-z_]*.*ZMod|ZMod.*mulVec' "$ML"
run "mathlib/ZMod.val_add"         grep -rnE '(theorem|lemma) (ZMod\.)?val_add\b|(theorem|lemma) (ZMod\.)?val_add_of_lt|(theorem|lemma) (ZMod\.)?val_add_le' "$ML/Data/ZMod"
run "mathlib/Nat.add_mod"          grep -rnE '(theorem|lemma) (Nat\.)?add_mod\b' "$ML"
LEANSRC=$(ls -d ~/.elan/toolchains/*v4.25.0*/src/lean/Init 2>/dev/null | head -1)
[ -n "$LEANSRC" ] && run "lean-core/Nat.add_mod" grep -rnE '(theorem|lemma) (Nat\.)?add_mod\b' "$LEANSRC"
run "mathlib/subset-sum-mulVec"    grep -rnE '(theorem|lemma) (Matrix\.)?(mulVec_single|vecMul_single|mulVec_sum|sum_mulVec|mulVec_add|vecMul_add)\b' "$ML/Data/Matrix" "$ML/LinearAlgebra/Matrix"
run "mathlib/Finset.exists_max_image" grep -rnE '(theorem|lemma) (Finset\.)?exists_max_image\b' "$ML"
run "mathlib/finSumFinEquiv"       grep -rnE '^(def|theorem|lemma|@\[simp\] theorem) finSumFinEquiv[A-Za-z_]*' "$ML/Logic/Equiv/Fin"
run "mathlib/Fin.append-defs"      grep -rnE '(def|theorem) (Fin\.)?append(_left|_right)?\b' "$ML/Data/Fin"
echo "log: $LOG"
