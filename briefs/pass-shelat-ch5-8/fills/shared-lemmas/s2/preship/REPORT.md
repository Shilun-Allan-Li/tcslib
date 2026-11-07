# S2 pre-ship checks

**PASS for issue-time API applicability, not completion of the host proof.**

Source ancestor `31348fcf7dee32f84db1fc8f929d80653137995e` is the user's #227 merge.
The complete library, root facade, toolchain and manifest match audited S1 head
`84f35910912bd3d1cd520beea9469e0ed45ce504`. All 437 recorded source fingerprints agree.
A separate tree copies only this chat's 437 project-module objects, including the audit module;
every copied object hash matches. Closure, Arithmetic and Concrete were then rebuilt from the
merged source and matched byte-for-byte before use. No dependency tree was copied or joined.

Native macOS preflight: 12 CPUs, 18 GiB physical memory, 6,019,858,432 bytes of the recorded
free+inactive+speculative-page headroom proxy, 482,163,073,024 bytes disk free. The proxy is
not Linux MemAvailable or a cgroup calculation. Present packages match all manifest pins;
no zero-length package objects. The 75 candidate roots and all 144 final-Checks roots are within the same session's successful
144-root narrowed cache closure, so no additional cache command was needed. A probe importing
one of those 75 roots passed. Fresh external workers still perform the attached addendum's
full setup/bootstrap: 94 candidate modules plus the remaining prerequisites of the
422-library-module Checks closure, followed by Checks.

## Fresh probe results

- All **38 public API checks** resolve; exact types are in `logs/Names.log`.
- The route probe seals **11 foreign definitions/matchers** and compiles with zero errors.
  It constructs an efficient below-modulus test from ArithmeticFP.le_poly and negation,
  specializes H15 to sampleBelowL, obtains a polynomial-time zero-default payload with the
  tail-length bound, specializes H15 to sampleUnitL with its supplied test hypotheses, and
  checks the T=0 boundary via the public find equation. Widths/stride/trials remain arbitrary.
- The tail route uses public `List.drop_one` through PolyTimeComputable.congr, since the
  polynomial-time tail primitive is stated as List.drop 1. It does not assume a true head bit
  or canonical/fixed-width success payload.
- Three route axiom prints include sorryAx from the deliberately admitted H15; the no-trials
  boundary uses standard axioms only. All four records/four distinct names are in summary.json.
- The exact repetition matcher control closes unsealed and fails once, at its proof, when
  sealed. Both logs and exact probe sources are retained.

The unit route assumes an efficient, correct acceptance test; this pre-ship phase does not
rebuild its gcd/inequality test. The worker must construct its actual consumer specialization
from the existing ArithmeticFP interfaces and prove all consumer re-points. These probes do
not prove H15 or replace delivery checks. This phase did not freshly replay all 94 candidate or 422 Checks-prerequisite modules;
the full native S1 baseline replay and source/byte-validated copy are distinct evidence.

The first route attempt had a wrong namespace for pairing and omitted tail/drop/β transport.
Its source and diagnostics are retained as `Routes-attempt1.source.txt` and
`logs/Routes-attempt1.log`; it is excluded from successful evidence. Only the corrected route
log counts. The initial 36-name probe was successful; the final 38-name probe adds the two
published bridge/name checks. One Lean process per dedicated tree was used throughout.
