# Original baseline reuse for final3

`baseline-reuse.json` verifies reuse of the original **final2** baseline runs;
their raw files remain under their actual original paths. It does not claim a
new final3 baseline check. The read-only generator is
`evidence/tools/baseline_reuse.py` (`python3 -I`, no Lean).

The record binds 256 original evidence files by SHA-256. It checks all 98
original module sources against Git base
`eff2dcd0a63f0c371118a17c67b9a5dfc046f4e9`, both the independent baseline
snapshot/runtime source copies, all 98 unchanged baseline oleans against their
original successful bootstrap records, Lean 4.25.0 and the exact package
manifest. Runtime oleans remain outside the delivery payload.

The reused native evidence is four zero-error whole-file base seals (both
original owners, A/B), eight passing paired base controls, the base native scan
and complete manual review of 208 items, and the original all-stored baseline
census of 172 constants. The raw census remains under
`evidence/logs/rule10/checkpoint1/base-collect/`; base seals/controls/scan and the
manual review remain under `evidence/.../rule10/final2/` and
`evidence/probes/Rule10/final2/` as applicable. The JSON lists every actual path.

For the fresh summary, use `--edition final3 --base-edition final2`, with the
original base census log and the actual successful fresh final3 census log.
The summary reads the original final2 base manifests/results/controls/scan
directly. It also rechecks reuse hashes and unchanged baseline source/object
bindings. Base rows carry `evidence_edition: final2`; final rows carry
`evidence_edition: final3`.

The completed optimization pilot remains the historical
`final2/seal-provenance.json`. It establishes that the unchanged 2048-request
harness uses the ordinary registered local attribute handler, retains complete
Name/component/mask checks, passes its controls, and agrees with the earlier
full base-A seal. Its actual old/new durations belong to those historical
runs. The reuse record confirms the generator/API bytes are unchanged.

That historical pilot does not certify the repaired proof bodies. The fresh
final3 snapshot, collector/census, all final seals, final controls, final native
scan/manual review and canonical final sweep must certify the delivered final3
sources. Only `Hashing/FromDiscreteLog.lean` and its `Reduction.lean` helper
differ from the final2 source snapshot; their new raw evidence must remain
identified as final3. The report should use `--base-edition final2` and
`--harness-edition final2` while reporting final3 as the fresh final edition.
