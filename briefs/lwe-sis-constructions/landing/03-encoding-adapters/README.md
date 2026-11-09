# Encoding adapter landing evidence for PR #238

The adapter branch incorporates central commit
`79331405f1136fea09f1c8dd5b7c6b99761e4776`, the merge of PR #237.
Merge `39a8453f868453eb5ee269cbaa73aa541c551764` preserves the Lean tree and
pins of the passing proof audit at `b9ce3521e7f5a15d80e71bf5e9be4c48bc73010e`.
The Lean delta adds `Encoding/BinaryArith.lean` and imports it in the Encoding
facade. It adds 20 declarations and discharges all 14 audited obligations.

| Check | Result |
|---|---|
| Landing replay | Adapter and Encoding facade checked serially, zero errors and admissions |
| Axiom probe | All 29 explicit prints and 284 owned constant inventories match the proof audit |
| Dependency closure | All 93 source hashes reconciled, 91 dependency objects reused from this branch's own audited sweep |
| Encoding style | Zero failures and warnings over three files |
| Reference scope | 37 previously approved attributions inherited, no new attributions or registry edits |

`landing-checks.json` and `check-output.log` record the replay. The native checks
ran before the merge against the identical Lean source, with the same package pins
and an isolated olean tree. The earlier fresh 93-module proof sweep records 17
inherited admission warnings. The landing replay covers the changed modules and
axiom probe. Whole-library root elaboration remains unchecked. The existing
blueprint, dataset and script inputs match the central tree.
