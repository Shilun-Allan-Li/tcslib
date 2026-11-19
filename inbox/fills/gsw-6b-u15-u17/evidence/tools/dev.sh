#!/usr/bin/env bash
# Dev check of a scratch Lean file against the bootstrap oleans (no olean output).
R=/workspace/gsw2/repo
LP="$R/.lake/tcslib-check-oleans"
for d in "$R"/.lake/packages/*/.lake/build/lib/lean; do LP="$LP:$d"; done
export LEAN_PATH="$LP" PATH="$HOME/.elan/bin:$PATH"
cd "$R"
timeout 1200 lean -DmaxErrors=30 "$1" 2>&1 | head -${2:-150}
echo "EXIT ${PIPESTATUS[0]}"
