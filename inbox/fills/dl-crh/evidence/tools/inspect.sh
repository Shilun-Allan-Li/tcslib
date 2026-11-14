#!/bin/bash
# Reproduce source/hash checks and the missing-reader search at the pinned base.
set -eu
WORKTREE="$1"
PAYLOAD="$2"
cd "$WORKTREE"
printf 'Proof checkout identity and changes:\n'
git rev-parse HEAD
git branch --show-current
git status --porcelain
git diff --exit-code eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9 -- TCSlib
printf '\nPinned issue-source hashes:\n'
shasum -a 256 -c "$PAYLOAD/evidence/inputs/SOURCE-SHA256SUMS"
printf '\nAll raw-generator and raw-sampler occurrences in TCSlib:\n'
rg -n 'expGenFun|expSampleRaw' TCSlib
printf '\nBundled representation/behavior readers:\n'
rg -n 'expGen|expSampler' TCSlib/Cryptography/Candidates/DiscreteLog.lean
printf '\nPublic NUPPT uniform-machine readers:\n'
rg -n 'output_ofPolyTimeUniform|coins_ofPolyTimeUniform|runAtL_ofPolyTimeUniform|runAt_eq|runAtL_eq' TCSlib/Complexity/Randomized/PPT.lean
printf '\nPotential raw readers (expect no matches):\n'
if rg -n '(theorem|lemma).*expGenFun_(eq|layout|spec|run)|((theorem|lemma).*expSampleRaw_(eq|layout|spec|run))' TCSlib; then
  printf 'REVIEW: a candidate reader exists\n'
else
  printf 'NO_MATCH: no named raw behavior reader\n'
fi
printf '\nScoped source excerpts:\n'
sed -n '475,564p' TCSlib/Cryptography/Candidates/DiscreteLog.lean
sed -n '636,645p' TCSlib/Cryptography/Candidates/DiscreteLog.lean
sed -n '712,727p' TCSlib/Cryptography/Candidates/DiscreteLog.lean
sed -n '59,88p' TCSlib/Cryptography/Hashing/FromDiscreteLog.lean
