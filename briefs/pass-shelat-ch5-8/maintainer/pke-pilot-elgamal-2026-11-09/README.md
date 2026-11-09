# ElGamal in public-key encryption

Seyoon merged the [DDH extraction #261](https://github.com/Shilun-Allan-Li/tcslib/pull/261) at `be34dc52367e5c4190d2aae5547d3260a75b85eb`.
[PR #262](https://github.com/Shilun-Allan-Li/tcslib/pull/262) moves the ElGamal construction, correctness theorem,
and DDH security reduction at `85feea8b82fdef6117a6819900ec66f09e7e93bd`. The
[approved PKE pilot](../cleanup-incremental-2026-11-09/final-r1/PKE-PILOT.md)
places the reusable assumption in `Candidates.DDH`.

The new PKE module is byte-for-byte identical to the old implementation.
The legacy candidate import re-exports it. The public-key facade imports
the new module directly.

- All 6 affected modules compile, including the library root and
  campaign Checks. The replay verifies 1,079 retained objects. The
  Checks object and output match the accepted #261 baseline.
- Both standalone import probes pass. The census matches all 180 declaration
  types, definitions, reference sets and axiom dependencies. It accounts for
  91 private names and compiler-generated binder labels at the new home.
- The whole-file seal repeats the previous 1,515 requests and passes.
  The focused Checks seal covers 33 relocated definitions.
  The thirteen sensitivity controls transfer through identical checked
  closures, and the generated-equation collector reruns both controls.
- The source scan maps the 4 inherited core reads to the new path with
  the same line numbers. `READS.json` records the original ledger IDs and both
  module locations.
- The 1,835-line module carries the inherited file-size finding and
  reader warnings. Keeping the body together preserves the private arithmetic
  used by both `dlc_poly_egEncParts` and `dlc_poly_ddhInput`, including
  `dlc_numPoly_egCanon` and `dlc_poly_natToList_powMulMod`. It also keeps the
  typed coin conversions in `dlc_challenge_eq` beside the construction fields
  they read. A separate split can establish those interfaces during the
  final layout and seal cleanup.

`VERIFICATION.json` binds the evidence to the checked source.
`elgamal-checks.zip` has SHA-256 `ad7cf0ac4480a8eba7c0b15766204563f85a9a708b40198c9895aa034da22634`.

**Clear to merge — the ElGamal move and legacy import pass.**
