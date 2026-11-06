#!/usr/bin/env bash
# Integration replay (scratch only): a copy of the dl-b olean tree; dl-a's Concrete and DiscreteLog
# (read from the dl-a worktree at its head) and dl-b's DiscreteLogHardcore, with every module of the
# order list from Concrete to DiscreteLogHardcore recompiled in order; then the axiom prints.
set -u
SP=/tmp/claude-0/-home-user-tcslib/d0667d12-db8d-5853-b0f7-9833dc0884c6/scratchpad
WT=$SP/wt-fill-dl-b; WA=$SP/wt-fill-dl-a; D=$SP/fillwork-dl-b; IO=$D/integ-oleans
ORDER=/home/user/tcslib/briefs/pass-shelat-ch5-8/fills/dl-candidates/inputs/dl-b/order.txt
LOG=$D/evidence/logs/integration-replay.log
rm -rf $IO; cp -r $SP/fill-dl-b-oleans $IO
LP="$IO"; for d in "$WT"/.lake/packages/*/.lake/build/lib/lean; do [ -d "$d" ] && LP="$LP:$d"; done
export LEAN_PATH="$LP"; export PATH="$HOME/.elan/bin:$PATH"
echo "integration replay $(date -u +%FT%TZ): dl-a head $(git -C $WA rev-parse HEAD), dl-b head $(git -C $WT rev-parse HEAD)" > $LOG
start=$(grep -n '^TCSlib/Cryptography/Candidates/Concrete$' $ORDER | cut -d: -f1)
stop=$(grep -n '^TCSlib/Cryptography/Candidates/DiscreteLogHardcore$' $ORDER | cut -d: -f1)
sed -n "${start},${stop}p" $ORDER | while read -r m; do
  case "$m" in
    TCSlib/Cryptography/Candidates/Concrete|TCSlib/Cryptography/Candidates/DiscreteLog) root=$WA ;;
    *) root=$WT ;;
  esac
  mkdir -p "$IO/$(dirname $m)"; rm -f "$IO/$m.olean"
  out=$(cd $root && lean "$m.lean" -o "$IO/$m.olean" 2>&1); rc=$?
  echo "== $m (from ${root#$SP/}) exit=$rc errors=$(printf '%s\n' "$out" | grep -c 'error:') sorry=$(printf '%s\n' "$out" | grep -c "declaration uses 'sorry'")" >> $LOG
  [ $rc -eq 0 ] || { printf '%s\n' "$out" >> $LOG; echo "REPLAY FAIL" >> $LOG; exit 1; }
done
cp $D/scratch/Axioms.lean $WT/.dlb_axioms_tmp.lean; (cd $WT && lean .dlb_axioms_tmp.lean) >> $LOG 2>&1; rm -f $WT/.dlb_axioms_tmp.lean
echo "REPLAY END $(date -u +%FT%TZ)" >> $LOG
