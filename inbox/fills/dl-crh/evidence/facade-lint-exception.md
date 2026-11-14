# Concrete lint exception request

The required command `python3 -I scripts/campaign_style_lint.py TCSlib/Cryptography --check8b`
reports 222 FAIL versus the issued tree's 216 FAIL. The exact six added diagnostics are
`facade does not import child module` for the six FromDiscreteLog helper modules in
`TCSlib/Cryptography/Hashing.lean`.

That frozen facade already directly imports `TCSlib.Cryptography.Hashing.FromDiscreteLog`,
which now directly imports all six helpers and lists all six in Contents. All helper
modules are therefore transitively exported. The lint at lines 345–353 recursively
checks every descendant against the ancestor's *direct* imports.

Proposed narrow disposition: acknowledge those exact six redundant-import diagnostics
as facade-lint false positives; preserve the frozen ancestor facade. This would be an
explicit user exception to the brief's literal no-new-FAIL requirement, not a claim of
zero mechanical new FAIL. Every other new FAIL remains forbidden.

Alternative concrete change (requires an additional freeze exception): append direct
imports of Algebra, Coins, Encoding, Probability, Reduction, Sampling to Hashing.lean.
No declaration or behavior change would result, but that would expand changed-file
scope and its evidence requirements.

## User decision

The user explicitly replied: “Acknowledge exactly six lint false positives”.
This permits exactly the six ancestor-facade diagnostics described above.
No frozen facade edit is made. The final report must retain raw counts and name
this exception; it must not claim a literal zero-new-FAIL lint result.
