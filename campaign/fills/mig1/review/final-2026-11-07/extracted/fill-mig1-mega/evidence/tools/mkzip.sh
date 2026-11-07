#!/usr/bin/env bash
# mkzip.sh <zipname-without-.zip> <REPORT.md path>: assemble, checksum, zip and verify a delivery.
set -euo pipefail
. /work/mig1/env.sh
NAME=$1; REP=$2; BASE=83ac315ed9e7089466bd16a32f3b71fbadc556d2
OUT=/work/mig1/deliver; ST=$OUT/$NAME; rm -rf "$ST" "$OUT/$NAME.zip"; mkdir -p "$ST"/{source,patches,evidence}
cd "$TCSLIB_REPO"
test -z "$(git status --porcelain -- TCSlib)" || { echo "dirty TCSlib tree"; exit 1; }
cp "$REP" "$ST/REPORT.md"
while read -r f; do mkdir -p "$ST/source/$(dirname "$f")"; cp "$f" "$ST/source/$f"; done < /work/mig1/packet/campaign/fills/mig1/inputs/owned-files.txt
git format-patch -q -o "$ST/patches" "$BASE..HEAD"
git bundle create "$ST/fill-mig1-mega.bundle" "$BASE..fill/mig1-mega" 2>/dev/null
git rev-parse HEAD > "$ST/HEAD.txt"; echo "$BASE" > "$ST/BASE.txt"
git log --format='%H %an <%ae> %cI %s' "$BASE..HEAD" > "$ST/COMMITS.txt"
cp -r "$EV/logs" "$ST/evidence/logs"
[ -d "$EV/seal" ] && cp -r "$EV/seal" "$ST/evidence/seal"
[ -d "$EV/screens" ] && cp -r "$EV/screens" "$ST/evidence/screens"
mkdir -p "$ST/evidence/tools"; cp /work/mig1/{sweep.sh,sweep2.sh,withslot.sh,chk.sh,axprobe.sh,mkzip.sh,env.sh,extract.py} "$ST/evidence/tools/"; cp -r /work/mig1/tools/. "$ST/evidence/tools/"
cp -r /work/mig1/ax "$ST/evidence/axiom-name-lists"
( cd "$ST" && find . -type f ! -name SHA256SUMS -print0 | sort -z | xargs -0 sha256sum > SHA256SUMS )
( cd "$OUT" && zip -qr "$NAME.zip" "$NAME" )
# verify
V=$(mktemp -d); ( cd "$V" && unzip -q "$OUT/$NAME.zip" && cd "$NAME" && sha256sum -c --quiet SHA256SUMS && echo "checksums OK ($(wc -l < SHA256SUMS) files)" )
git bundle verify "$ST/fill-mig1-mega.bundle" 2>&1 | tail -2
( cd "$V" && git init -q b && cd b && git fetch -q "$TCSLIB_REPO" "$BASE" 2>/dev/null; git fetch -q "$V/$NAME/fill-mig1-mega.bundle" fill/mig1-mega:t && echo "bundle head $(git rev-parse t)" )
rm -rf "$V"
sha256sum "$OUT/$NAME.zip"; ls -la "$OUT/$NAME.zip"
