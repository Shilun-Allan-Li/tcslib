# Source-fidelity documentation patch proposals

**Unapplied documentation-only proposals.** Frozen source head supplied by root: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
No Git command, Lean/cache command, app, or library edit was used to generate these patches.
Root will apply them only after the initial surveys; they are not part of the frozen source.

| File | Frozen source SHA-256 | Proposed file SHA-256 | Patch |
|---|---|---|---|
| `TCSlib/Cryptography/Composability/NonMalleable.lean` | `db1edf1a7d56885e29a7103d3b8bb13277e3db93fb77a1791a7316c8eb06565a` | `275df4f1ea170d47393f1722793d11bd9340f55e532b8ee741d939ec170e6aca` | `NonMalleable-doc-source-fidelity.patch` (20 lines) |
| `TCSlib/Cryptography/Composability/SequentialZK.lean` | `323bbcbd042abeabdc408e2a64a808b8e3ffb9cfd20601093f2ab3d9e3391062` | `ff83de2b5ae739f2dc712950974705ccd1bbfade18628ccaed40eac569c0fa1d` | `SequentialZK-doc-abort-premise.patch` (56 lines) |

The normalized code outside block comments is identical before/after each proposal. Public
headers, definitions, proof bodies and admission tokens are unchanged. The existing `msgLen(n) = 0`
caveat in the non-malleability proof sketch is untouched, and the module note explicitly retains it.

- NonMalleable distinguishes PSV06's collapsed challenge-copy/invalid output from PSV07's COPY
  convention, and points to the existing complementary-pair copy-flag export sketch. The
  one-challenge comparison yielded no statement counterexample in the source review; a
  many-challenge bridge is not asserted. No part of SimNonMalleable is edited by these patches.
- SequentialZK states the strict-PPT abort premise, bounded independent retries and their
  geometric failure bound, then composition. PS10's expected-time wording remains separate
  from a claim about truncating arbitrary expected-time computation.

**Not yet clear to merge — these proposals remain unapplied; root-coordinated survey/seal repairs and verification remain.**
