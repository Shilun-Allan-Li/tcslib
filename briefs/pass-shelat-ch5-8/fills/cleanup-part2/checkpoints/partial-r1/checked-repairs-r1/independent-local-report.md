# Frozen local repairs: independent static review

**Local-delta verdict: 0 blockers, 0 majors, 0 minors.** The eight logical repairs stay within the stated proof/interface scope. This is not full cleanup, native or seal acceptance.

Reviewed inputs are only local-repairs-final-r1/src, manifest.json and repairs.patch against immutable received payload/src at delivery `0c4d4f60203021f3a3b93f88eaf7c9085c6ab885`. The manifest declares materialized base `bf2d8df1663f51c29a1d3c55ad8bf3fa56b74fe3`; no Git identity or native result was rerun here. Source SHA-256 identities, rather than later commit metadata, bind this review.

Own Python3-I validation checks all eight overlay hashes and exactly replays the patch in memory against the received bytes, including hunk positions/counts/context and Git blob prefixes. It finds:

- Eight consumer paths, zero provider paths; no provider proof edit.
- One removed theorem: NUPPT.ofPolyTimeUniform_def. It was newly introduced by this fill, absent at the issued ancestor. All its references disappear across the 221 source snapshots.
- Seven changed existing proofs: three output-reader substitutions and four unary-computability repairs. Zero added declarations, helper definitions, general lemmas or hosts.
- Every retained declaration header, data/algorithm body, visibility/modifier and attribute is byte-identical. All 20 owned admitted blocks remain exact; no admission was added, filled, moved or hidden by the removal.
- Five precise imports added across four files, none removed. The 1,071-module overlay graph remains acyclic with no missing local import. Docs now describe the actual BinArith/normalization route; existing theorem claims and costs remain unchanged.

The operational substitutions use the existing public output_ofPolyTimeUniform equation after public run wrappers. They remove the raw whole-machine equality without changing a machine, coin/advice field or activation claim. This resolves the local source issue PARTIAL-SRC-01 in this pinned overlay; the original incoming review remains immutable history.

The unary proofs compose the existing polynomial-time mulU routine with the existing unary-length map, then transfer through PolyTimeComputable.congr and length_mulU. Normalizing length matters because mulU copies its second word's contents; the result is therefore the required all-true word even for arbitrary Boolean inputs. The EncodingMachines case also uses length_replicate. Empty lengths yield the empty word without positivity premises. In the GI match-shaped theorem, pairDecode none gives two empty total projections through pairFstD_eq/pairSndD_eq; the explicit none/some branches preserve malformed-input semantics. No machine body is unfolded to recover a bare existential computation witness.

Every explicit item newly added to these proofs is a published theorem, verified against the received native kind metadata, including Core/Mathlib entries. The retained explicit glPad/glPadSampleFun bodies are local to their respective files. No new explicit foreign-definition read, generated-equation reference, unsafe command, admission shortcut or reducibility option appears. This does not assert that every unchanged inherited read elsewhere has been repaired.

The validation script, complete local declaration maps, changed proof blocks, patch replay and input hashes are retained beside this report. Only own reviewed utility code ran; no incoming program, Lean/cache/build/app, Git/source/main/exchange mutation or frozen-report edit occurred.

Root reports 124 current-source module checks, ten standard-only actual axiom sets, instance eligibility and zero new local style findings. Those remain Root's native-fixes-r1 records; this review neither reruns nor independently adopts them. Full corrected seals, broader partial work and draft-PR acceptance remain separate.

**Not yet clear to merge — the local repairs pass static review; the received cleanup remains partial and full seal acceptance is outstanding.**
