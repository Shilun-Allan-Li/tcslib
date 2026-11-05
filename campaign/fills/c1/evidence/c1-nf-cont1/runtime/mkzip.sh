#!/usr/bin/env bash
# mkzip.sh <zipname> <verifydir> <report.md> [extra evidence dirs...]
set -u
cd /home/user/tcslib
ZN="$1"; VD="$2"; REP="$3"; shift 3
BASE=348781a383f102d971fca153c818026b4f49fbf6
ST=$(mktemp -d /tmp/claude-0/-home-user/e83f8996-d545-513c-8228-08a794edf16c/scratchpad/zip.XXXX)
R="$ST/${ZN%.zip}"; mkdir -p "$R"/{source/TCSlib/Complexity/ClassNP,patches,bundle,evidence/logs,evidence/checks,evidence/seal,evidence/probe,evidence/runtime}
cp "$REP" "$R/REPORT.md"
cp TCSlib/Complexity/ClassNP/NDNormalForm.lean "$R/source/TCSlib/Complexity/ClassNP/"
git format-patch -q -o "$R/patches" $BASE..HEAD
git bundle create -q "$R/bundle/fill-c1-nf-cont1.bundle" $BASE..fill/c1-nf-cont1
git bundle list-heads "$R/bundle/fill-c1-nf-cont1.bundle" > "$R/bundle/heads.txt"
git bundle verify "$R/bundle/fill-c1-nf-cont1.bundle" > "$R/bundle/verify.txt" 2>&1
for f in evidence/logs/*; do skip=0; for pat in ${EXCL:-}; do case "$(basename "$f")" in $pat) skip=1 ;; esac; done; [ $skip = 0 ] && cp "$f" "$R/evidence/logs/"; done
for f in tail.log tail-summary.tsv walk-raw.log walk-ext.tsv walk-new.txt new-decls.txt axioms-raw.log inspection.md \
         lint-campaign.txt lint-style.txt size.txt rule11.txt reached-defs.txt; do
  [ -f "$VD/$f" ] && cp "$VD/$f" "$R/evidence/checks/"; done
cp scratch/NFAxioms.lean "$R/evidence/checks/NFAxioms.lean"; cp scratch/NFWalk.lean "$R/evidence/checks/NFWalk.lean"
for f in NFSeal.lean seal-block.lean seal-set.txt seal-module.log NFSealCtl_unsealed.lean NFSealCtl_sealed.lean \
         controls-unsealed.log controls-sealed.log; do [ -f "$VD/$f" ] && cp "$VD/$f" "$R/evidence/seal/"; done
for f in NFProbeExt.lean probe-run.log probe-names.txt cited-names.txt probe-extra.txt; do
  [ -f "$VD/$f" ] && cp "$VD/$f" "$R/evidence/probe/"; done
for d in "$@"; do cp -r "$d" "$R/evidence/"; done
cp /tmp/claude-0/-home-user/e83f8996-d545-513c-8228-08a794edf16c/scratchpad/bin/*.sh /tmp/claude-0/-home-user/e83f8996-d545-513c-8228-08a794edf16c/scratchpad/bin/*.py "$R/evidence/runtime/"
cp scratch/walk.lean.txt "$R/evidence/runtime/"
( cd "$R" && find . -type f ! -name SHA256SUMS | sort | xargs sha256sum > SHA256SUMS )
mkdir -p /home/user/tcslib/deliveries
( cd "$ST" && rm -f "/home/user/tcslib/deliveries/$ZN" && zip -qr "/home/user/tcslib/deliveries/$ZN" "${ZN%.zip}" )
rm -rf "$ST"
ls -la "/home/user/tcslib/deliveries/$ZN"; sha256sum "/home/user/tcslib/deliveries/$ZN"
