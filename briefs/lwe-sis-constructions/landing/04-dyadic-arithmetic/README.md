# Dyadic scalar arithmetic landing evidence for PR #239

The scalar arithmetic branch incorporates central commit
`0126e4de9ee28c84acd8ddf29974adb5109b0f4e`, the merge of PR #238.
Merge `d1ffc443dda8652492e9dc8d59ff72835291c682` preserves the Lean tree and
pins of the passing proof audit at `ec72ed773a690c17ac253707350935cc9e0acb34`.
The Lean delta adds `Encoding/DyadicArithmetic.lean` and imports it in the
Encoding facade. It adds 18 declarations and discharges all 12 audited obligations.

| Check | Result |
|---|---|
| Landing replay | Scalar arithmetic and Encoding facade checked serially, zero errors and admissions |
| Axiom probe | All 34 explicit prints and 302 owned constant inventories match the proof audit |
| Dependency closure | All 94 source hashes reconciled, 92 dependency objects reused from this branch's own audited sweep |
| Encoding style | Zero failures and warnings over four files |
| Reference scope | 37 previously approved attributions inherited, no new attributions or registry edits |

`landing-checks.json` and `check-output.log` record the replay. The native checks
ran before the merge against the identical Lean source, with the same package pins
and an isolated olean tree. The earlier fresh 94-module proof sweep records 17
inherited admission warnings. The landing replay covers the changed modules and
axiom probe. Whole-library root elaboration remains unchecked. The existing
blueprint, dataset and script inputs match the central tree.
