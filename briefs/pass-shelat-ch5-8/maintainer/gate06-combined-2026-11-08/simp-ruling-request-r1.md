# Six existing Gate06 simplification rules

Source: `a495f3953afff46ad5dec2d29ac8a7f55bd8ae37`; actual source preparation
base: `067c5d8d6dd436e62681d7dc607984c705dc80a2`.

Policy §1 says: “None carries `@[simp]` unless a gate approves it.” These six
attributes are new relative to the PR base and unchanged from audited
`3f6db40e1688c4a0bb922c9575dd3bd2157a650b`. Gates06B/C/D individually approved
the theorem statements. Their packs did not explicitly audit global rewrite
registration, and no separate attribute approval was found. No approval is
inferred merely from the absence of a finding.

| File / existing declaration | Rewrite result |
|---|---|
| `Composability/PublicKey.lean`: `pairFstD_padCt` | Decoding the first component of a padded ciphertext gives the original ciphertext. |
| `Randomness/BPPBridge.lean`: `eval_polyLenExpr` | Evaluating the syntactic polynomial gives `Randomized.polyLen a k n`. |
| `SecureComputation/Hybrid.lean`: `pairFstD_privA`, `pairFstD_privB` | Decoding the first component of a party's augmented input gives that party's original input. |
| `SecureComputation/Hybrid.lean`: `pairSndD_privA`, `pairSndD_privB` | Decoding the second component gives that party's ideal answers. |

The exact current declarations are at PublicKey96, BPPBridge64 and
Hybrid126/131/136/141. Each removes a decoding/evaluation wrapper; the six rules
do not reverse one another. This observation is not a global termination proof
or a substitute for the remaining native and rule10 checks.

Recommendation: approve **exactly these six existing global attributes** as
Gate06 normalization rules. This preserves the audited source and does not
approve arbitrary future simp registrations, foreign-definition reads, proof
admissions or deferred cleanup. The alternative is to remove their global
attributes, repair affected automation through explicit lemma applications,
and verify the changed source again.

Exact introduction commits, source hashes, gate-pack scope, individually
reviewed theorem rows and unchanged declaration comparisons are retained in
`source-review/final-static-r1/simp-attribute-provenance.json`. All source and
attribute text remains unchanged pending the user's ruling. Native work can
continue on the existing frozen source while this ruling is pending.

**Not yet clear to merge — native verification and this narrow policy ruling remain.**
