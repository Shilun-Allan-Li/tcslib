#!/usr/bin/env bash
S=$S
R=<repo>; B=6cfee54474e3d954e3395f9d9eab5d025452a8dd
cd $R
f=campaign/fills/u2s/briefs/u2s-fill-startup-cont1.md
echo "# dispatch copy"; shasum -a 256 exchange/outbox/fills/u2s-fill-startup-cont1.md
echo "# records copy (wt-hk)"; shasum -a 256 $S/wt-hk/$f
echo "# base copy"; git show "${B}:$f" | shasum -a 256
echo "# base copy with @ANCESTOR@ := base"; git show "${B}:$f" | sed "s/@ANCESTOR@/$B/g" | shasum -a 256
echo "# diff dispatch vs base-substituted"; diff <(git show "${B}:$f" | sed "s/@ANCESTOR@/$B/g") exchange/outbox/fills/u2s-fill-startup-cont1.md && echo SAME
echo "# diff records(wt-hk) vs base"; diff <(git show "${B}:$f") $S/wt-hk/$f && echo SAME
echo "# @ANCESTOR@ count in base copy: $(git show "${B}:$f" | grep -o '@ANCESTOR@' | wc -l)"
echo "# cover brief, addendum (base vs wt-hk)"
for g in campaign/fills/megafill/briefs/megafill-B.md campaign/standards/fill-environment-addendum.md; do
  echo "$g base:$(git show "${B}:$g" | shasum -a 256 | cut -c1-16) wt-hk:$(shasum -a 256 $S/wt-hk/$g | cut -c1-16)"
done
echo "# outbox"; ls exchange/outbox/fills/ | grep -i -E 'megafill|addendum'
for g in exchange/outbox/fills/megafill-B.md exchange/outbox/fills/fill-environment-addendum.md; do [ -f $g ] && shasum -a 256 $g; done
echo "# outbox megafill-B vs base (subst)"; diff <(git show "${B}:campaign/fills/megafill/briefs/megafill-B.md" | sed "s/@ANCESTOR@/$B/g") exchange/outbox/fills/megafill-B.md >/dev/null && echo SAME || echo DIFF
echo "# outbox addendum vs base"; diff <(git show "${B}:campaign/standards/fill-environment-addendum.md") exchange/outbox/fills/fill-environment-addendum.md >/dev/null && echo SAME || echo DIFF
echo "# inputs: base vs wt-hk"
for g in $(git ls-tree -r --name-only "$B" campaign/fills/u2s/inputs/u2s-fill-startup-cont1/ campaign/fills/u2s/orders/u2s-fill-startup-cont1.txt; git ls-tree -r --name-only "$B" campaign/fills/u2s/logs/ | grep startup-cont1); do
  echo "$g base:$(git rev-parse "${B}:$g" | cut -c1-12) wt-hk:$(git -C $S/wt-hk rev-parse "HEAD:$g" | cut -c1-12)"
done
