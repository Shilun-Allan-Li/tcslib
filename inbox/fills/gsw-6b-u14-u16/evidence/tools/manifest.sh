#!/usr/bin/env bash
# Copy the tools into evidence/tools, write evidence/SHA256SUMS and the top-level SHA256SUMS
# (every delivered file under the delivery directory except itself), and verify both manifests
# against the delivered paths.  Usage: manifest.sh <tool>...
set -e
D=/workspace/exchange/inbox/fills/gsw-6b-u14-u16; EV=$D/evidence
mkdir -p $EV/tools
(cd /workspace/u1416-tools && cp --parents "$@" $EV/tools/)
(cd $EV && find . -type f ! -path ./SHA256SUMS | sed 's|^\./||' | sort | xargs sha256sum > SHA256SUMS)
(cd $D && find . -type f ! -path ./SHA256SUMS | sed 's|^\./||' | sort | xargs sha256sum > SHA256SUMS)
(cd $EV && sha256sum -c --quiet SHA256SUMS && diff <(find . -type f ! -path ./SHA256SUMS | sed 's|^\./||' | sort) <(sed 's|^[0-9a-f]*  ||' SHA256SUMS | sort) && echo "evidence manifest: $(grep -c '' SHA256SUMS) files, paths equal")
(cd $D && sha256sum -c --quiet SHA256SUMS && diff <(find . -type f ! -path ./SHA256SUMS | sed 's|^\./||' | sort) <(sed 's|^[0-9a-f]*  ||' SHA256SUMS | sort) && echo "top-level manifest: $(grep -c '' SHA256SUMS) files, paths equal")
