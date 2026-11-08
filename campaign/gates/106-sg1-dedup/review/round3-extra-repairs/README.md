# Gate106 round3: two additional proof-only repairs

**Implemented; final exact-header native/sealed probes PASS. Not yet clear to merge: #215.**
Only the approved private bodies clA5Pair_sizes and clA5Le_native, plus their adjacent accurate
sketches, changed in Hardness. Every old full header/import/attribute/order/definition/table
and other body is frozen. Reversing exactly the two replacements reconstructs the complete
before file. Prior13-review payloads were verified unchanged; SAT and all image/iteration/
drop-design candidates were untouched. No commit/push/Git mutation, screen, cache/snapshot
write or compiled output occurred.

## Exact repairs

- **clA5Pair_sizes:** one case split on pairDecode. Failure gives empty defaults. Success
  uses eq_pairEncode_of_pairDecode and length_pairEncode, then arithmetic bounds both
  components. The change step reduces only unchanged same-home clHeaderField/clHeaderTail
  zero/one cases. The foreign decoder stays opaque; no recursive decoder unfolding remains.
- **clA5Le_native:** polyTimeComputable_lenLe is composed with hg.pairEncode hf, in the
  required reversed order. Published pairFstD_pairEncode/pairSndD_pairEncode and
  List.length_replicate identify f≤g. No oracle, new hypothesis or weakened statement appears.

The initial exact-header native/sealed owner-context probes passed before actual mutation.
They copy only the two unchanged private same-home field definitions into a scratch namespace;
there is no foreign private alias or hypothetical reader. Both exact new headers are literal
copies from actual source. Full actual Hardness v1 then passed natively and with the two
actual sections guarded before their complete docs/headers.

## Versions and tested limits

| Version / input | Result | Limit |
| --- | --- | --- |
| Small-native-v1 / Small-sealed-v1 | Both exit0/errors0 | Two unused local hd simp-argument warnings |
| Hardness-native-v1 / Hardness-sealed-v1 | Both full actual module inputs exit0/errors0;2 roots+2 descendants standardAX | About166/175seconds each; full v1 source has those two extra warnings |
| Small-native-v2 / Small-sealed-v2 | Both exit0/errors0/warnings0;2 roots+2 descendants standardAX | Final exact bodies after deleting only the two unused hd simp arguments |
| Fresh20-definition controls |40 kernel-checked positives /40 exact sealed failures; checker corruptions rejected | Exact identities/multiplicities; decoder uses nil and abstract separator-suffix controls |

**Final whole-module native/seal was NOT rerun after that two-argument warning-only cleanup.**
The bounded task stops here; root's already planned combined15-root metadata/full native/
replay checks must cover the final current source. Neither the v1 full-module pass nor the
v2 small pass is misreported as a final-source full replay. No gate/merge readiness is claimed.

The20-def guard extends the prior18 with ordinary pairFstD/pairSndD; default Action.apply,
Cfg.init and initCfg simp attributes are disabled. All directly reached foreign ordinary
names are guarded: PolyTimeComputable, pairFstD, pairSndD, pairDecode and pairEncode. Core/
public equation simplifier arguments are explicit; same-home field reads are identified.
No direct imported private name is cited. All recorded selected AX sets contain only the
standard three or fewer. Complete raw logs and source/request/run hashes distinguish every
version and its warnings. Removing only the scratch v1 guard sections reconstructs native
v1 exactly. The final v2 local native/seal sources also differ only by the same guard.

The source-only cleanup checker first used an over-specific diff-line count and stopped
before any source mutation; its error is retained. Corrected checking constrains the cleanup
to exactly the two newly added simp lines. No Lean proof attempt failed. The initially unused
hd arguments are removed without suppressing any linter.

## Final source and handoff

Current Hardness SHA256:
`3aab2fcb78b1a21aa621e2121f7b5fd04a27ace2bc2018e317032c8c2873706d`.

The fully tested v1 SHA256 was
`50df6303c957a5f5ccb3b2c9dc482433c406cb136581e54077ab7c9012ae625b`.
The pre-extra source (prior13 repairs) was
`34e1353242bcfa3aafbb19eaea2087d0e62860dfebbb545dd3bfd6d0b0fb716d`.
All three full sources, both diffs and both change records remain inert .lean.txt/JSON data.
Root owns the combined15-root full-source validation, integration/replay, commit/push,
ledger/source-screen/pack refresh and the user-selected Codex106 round3 audit. No design,
public API, new import or acknowledgment is granted by this repair.
