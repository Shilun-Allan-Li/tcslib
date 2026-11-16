#!/usr/bin/env bash
# chk.sh ROOT MODULE LOG : check one module with ROOT/scripts/lean_check_tree.sh under the lock,
# then count both error forms (error: and error( ) and sorry warnings.
set -u
export PATH=$HOME/.elan/bin:$PATH
ROOT=$1; MOD=$2; LOG=$3
mkdir -p "$(dirname "$LOG")"
cd "$ROOT" && python3 -I /home/user/tools/runlean.py "$LOG" -- bash scripts/lean_check_tree.sh "$MOD" > /dev/null
st=$?
ne=$(grep -cE '^\S+\.lean:[0-9]+:[0-9]+: error[:(]' "$LOG"); ns=$(grep -c "declaration uses 'sorry'" "$LOG")
echo "$MOD exit=$st errors=$ne sorry_warnings=$ns $(tail -1 "$LOG" | sed 's/.*start=/start=/')"
exit $st
