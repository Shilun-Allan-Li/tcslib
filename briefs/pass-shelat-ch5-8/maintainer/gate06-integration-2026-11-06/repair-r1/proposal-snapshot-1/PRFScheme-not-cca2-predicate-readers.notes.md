# PRFScheme: final non-CCA2 implication through public predicate readers

**UNAPPLIED; native elaboration and sealed replay pending.** Frozen source head supplied by
root: `e9d64158461bfe24ddc88ab885bc4017899b4c16`. Current source SHA-256 matches the completed
original seal manifest. No library edit, Lean/cache command, Git command, or app was used.

## Exact target and diagnostics

The target is **`TCSlib.Cryptography.Composability.not_prfFixedScheme_cca2`**, the final proved
implication from Claim 169.a's admitted advantage-one witness to failure of CCA2 security.
It is distinct from `prfFixedScheme_not_cca2`, whose existing admission remains unchanged.

The completed ordinal-14 probe has valid installation/EOF markers for all 1,751 requests
(1,732 active, 19 already irreducible). Its diagnostics map as follows:

| Probe line | Frozen source line | Cause | Scope |
|---|---|---|---|
| 1880 | 61 | Generator tape type mismatch after implicitly reading foreign `prfScheme` data | Untouched; separate future invocation. |
| 1965 | 146 | `h : S.INDSecure .cca2` is applied to `A q` while the foreign predicate is sealed | Addressed in this proposal. |
| 1965 | 146 | `rcases`/`obtain` receives an unresolved result after the invalid application | Cascading diagnostic from the same application. |

## One-block repair

Only the existing tactic block of `not_prfFixedScheme_cca2` changes. First rewrite `h` through
`FixedLengthScheme.INDSecure_iff`, then retain the existing extraction of the adversary's
negligible advantage bound. The same block next applies `hε : Negligible ε` to exponent zero;
`Negligible` is also in this full seal set. Rewrite it through `negligible_iff` before that
application. This second public reader prevents a further foreign-predicate read in the same
repaired proof; it is not a new theorem or a change to the security notion.

Both new `rw` entries are public theorems, homed respectively at
`Composability/Defs.lean:291` and `Foundations/Negligible.lean:62`. No definition is named in
an unfolding list. The original contradiction argument, headers, hypotheses, algorithms,
data fields and every admission are preserved. No helper or additional tactic block is added.
The theorem still depends on the existing admitted Claim 169.a; this is an interface repair,
not a substantive security proof fill.

The generator-tape diagnostic at source line 61 is deliberately untouched. Native replay
may expose additional diagnostics, so this proposal does not claim the module's seal passes.

## Fingerprints and static validation

| Artifact | SHA-256 |
|---|---|
| Frozen `PRFScheme.lean` | `27e85230b94478b31362ed71d385f53f48f2d56695aa75683f8416b131308927` |
| Proposed `PRFScheme.lean` | `3738c3d26d545ebe43a4f02cb5fef3721aed0196ab4af2d45d7072991ce8b4f6` |
| Proposal patch | `4813e8c4ab9ba334d095a35dd2c4be326761c2c2c1a121768f7f6bf9114847ab` |
| Public IND-reader home `Defs.lean` | `20b050712fb25b78b0b9e277a2f80ab110220097e30f0e6d7d521ff9f34e8679` |
| Public negligibility-reader home | `5e6d2c9e69dbfe012c36a92bad05ec27e691c044dae73a7277b9599902074e1a` |
| Original completed seal log | `1bfe44e0530eccdbfd5a2e9c131e7d2584e2c5f50d6904dd162451cfe8785794` |
| Original seal manifest | `75b11d1cf5324eea8066b898e5c37a677de266513cdde4be697ef8bf8149ba73` |

The sole patch hunk was applied independently in memory and reproduced the proposed source.
All bytes outside the target proof block, its public header, and admission-token counts were
checked unchanged. Root retains patch application and native verification ownership.
