#!/usr/bin/env bash
# deliver.sh "<commit message>" : copy the payload to inbox/fills/adaptive-cpa/ on the exchange and push
set -e
MSG="$1"; P=/home/user/acpa/payload; EX=/home/user/ex; D=inbox/fills/adaptive-cpa
cd $EX
git fetch -q origin exchange/pass-shelat-ch5-8
git checkout -q -B xfer-acpa origin/exchange/pass-shelat-ch5-8
git status --short | head
rm -rf $D; mkdir -p $D; cp -r $P/. $D/
git add -A $D
git commit -q -F - <<MSGEOF
$MSG

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01PqpVTm8SAfk12DMX1esC2g
MSGEOF
echo "outside-path files: $(git show --name-only --format= HEAD | grep -v "^$D/" | wc -l)"
for i in 0 1 2 3 4; do
  git pull -q --rebase origin exchange/pass-shelat-ch5-8 && git push -q origin HEAD:exchange/pass-shelat-ch5-8 && break
  sleep $((2 ** (i + 1)))
done
git log --oneline -1
