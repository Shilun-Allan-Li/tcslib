# CCA2Scheme: second independent coin-length proof proposal

**UNAPPLIED; native elaboration and sealed replay pending.** Frozen head supplied by root:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. Current source matches the frozen fingerprint.
No library edit, Lean/cache command, Git command, or app was used in this invocation.

Only the existing local `hr` proof at frozen source line **322** changes. This is diagnostic
probe line **2094**, within `ccaScheme.correct`, in the completed initial whole-file seal.
The previous generator-count proposal is a separate artifact and is unchanged.

The original `simp; rfl` leaves `(ccaEnc hE).coinLen n = n`; its final conversion reads the
foreign `NUPPT.coinLen` and uniform-machine constructor bodies. The replacement uses only
`List.length_ofFn`, `NUPPT.coinLen_eq`, `NUPPT.coins_ofPolyTimeUniform`, and
`PolyExpr.eval_var`. The local `ccaEnc` abbreviation expands only to match the public reader.
One existing tactic block changes; definitions, data fields, public headers, all other proof
blocks, and admissions are unchanged. No new declaration or admission is introduced.

## Application order and static composition

1. `CCA2Scheme-correct-gen-coins-reader.patch` (the previous source-line-320 proposal).
2. `CCA2Scheme-correct-enc-coins-reader.patch` (this source-line-322 proposal).

This patch uses one context line on each side, excluding the generator-count line modified by
step 1. Exact context matching and in-memory application succeeded both on the frozen source
and after step 1 (the latter shifts this proof to line 324 before application). Reverse order
is not asserted, since the earlier proposal has wider context containing this proof.
These checks do not establish Lean elaboration or passing seals.

| Artifact | SHA-256 |
|---|---|
| Frozen `CCA2Scheme.lean` | `c361af28d05eb36cbbfe91d43c0f9b6856d9abf98e7ed4bfaf2e6cff433cb70b` |
| Previous generator-count patch | `ac644eb1ed3d76b21090cc1b3b523c9c1c0c72336b86a7be93e5fc92eb82118e` |
| This encryptor-count patch | `495d121f73ea23071af855ffdb2cb65b83ae50d670a81d770e919e2b370f0ce1` |
| Source after this patch alone | `85f276ed71902cf415bded73377978d7e3e6011f787b5fc817094713551eef46` |
| Source after previous patch alone | `508940311f491e5555202920c4e44e6b61a65ffd5eea4ab546620bc41eba5cff` |
| Source after both in the stated order | `92d253838b287d5bfcfa73165cd088cb2da2666395de0344f05700854ab247c6` |

The two original diagnostics at frozen source lines **332** and **335**, in
`ccaScheme.enc_length`, remain untouched by both proposals. They have the same missing
public-reader conversions for generator and encryptor coin lengths. No further proof block
was written in this invocation. Root retains native checking and application ownership.
