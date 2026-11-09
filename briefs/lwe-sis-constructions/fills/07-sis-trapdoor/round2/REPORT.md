# Gate 12 round 2 repair

The user approved the exact F01 patch published at
`089c8dacf161a475ffff85b1b108b11529bd094c`. The repair is committed on draft #250 at
`93dc88648f117877e42aaf58ba7b911c76a4b63a`. The committed diff matches the approved patch byte for byte.
[Approved patch](../intake-r1/proposed-binary-error-sum.patch)

One public theorem in `LWE.Basic` owns the binary subset-sum proof. The Regev
and lossy column bounds use it with their existing signatures. The precise
Mathlib import serves the moved proof. The lossy module imports the owner.
The F02 PW10 citation and overview fixes remain in the separate comment-only
commit `d3bb52db5aaf249a35e83506371a3c86e76cb69a`.

| Check | Result |
|---|---|
| Source delta from round one | Four changed library paths, 149 of 153 pinned files byte-identical |
| Prior type probe | All 220 exact level parameter and type representations preserved |
| Native scope | 144 modules across seven facades, 351.052 s, zero errors |
| Admissions | 18 owned and 17 inherited, with matching warning payloads |
| Axiom probe | 309 explicit prints, 610 owned constants, 63.699 s |
| Constant delta | One approved theorem, 0 added compiler auxiliaries, 0 removed compiler auxiliaries |
| Retained constants | All 609 retained constants preserve their identity and exact axiom sets |
| Style | Zero failures and two unchanged warnings over 41 files |
| Merge preview | `79ea2632d6879cb22b51660ea972ff7ff84bdf0f` at target `41aaf0a1acf29318fa8d741dadd9f5f585e43c93` preserves the checked library, root, and pins |

The fresh object tree and existing pinned package objects belong to this
worktree. Native checks ran serially through `scripts/lean_check_tree.sh`.
The sandbox permits memory and disk checks and denies process listing. The
existing local job receipt was complete at preflight. The native scope covers
the seven facades and two probes. The whole-library root was compared at
source.

**Not yet clear to merge.** Gate 12 requires independent re-audit. The 18
admissions, scoped source review, and landing checks remain open.
