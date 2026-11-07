# CCA2Scheme: final encryption-coin length proof proposal

**UNAPPLIED; native elaboration and sealed replay pending.** Frozen head supplied by root:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. Current source retains its frozen fingerprint.
No library edit, Lean/cache command, Git command, or app was used in this invocation.

Only the existing local `hr` proof at frozen source line **335**, in `ccaScheme.enc_length`,
changes. This is diagnostic probe line **2107**. The replacement reads the coin count through
`List.length_ofFn`, `NUPPT.coinLen_eq`, `NUPPT.coins_ofPolyTimeUniform`, and
`PolyExpr.eval_var`, instead of converting the sealed foreign definitions with `rfl`.
Exactly one existing proof block changes; definitions/data fields/headers/admissions and
all other proof blocks are untouched. No helper, public declaration, or admission is added.

## Composition of the four proposals

Apply the first three patches in the order below, then
`CCA2Scheme-enc-length-enc-coins-reader.patch`. Exact-context in-memory application passed for
this fourth patch alone and after all three preceding proposals. The three preceding patches
shift the target to line 341 before this fourth patch is applied.

| Earlier proposal | Patch SHA-256 | Source SHA-256 after that step |
|---|---|---|
| CCA2Scheme-correct-gen-coins-reader.patch | `ac644eb1ed3d76b21090cc1b3b523c9c1c0c72336b86a7be93e5fc92eb82118e` | `508940311f491e5555202920c4e44e6b61a65ffd5eea4ab546620bc41eba5cff` |
| CCA2Scheme-correct-enc-coins-reader.patch | `495d121f73ea23071af855ffdb2cb65b83ae50d670a81d770e919e2b370f0ce1` | `92d253838b287d5bfcfa73165cd088cb2da2666395de0344f05700854ab247c6` |
| CCA2Scheme-enc-length-gen-coins-reader.patch | `c09a9240c7d4686d80fe5815de6909be4e32767df536d7b87cca2ee55ef9c0fe` | `c0997797cf9f736aadb3c423be31ca9b3950ce8292df6f885e328d4741c016e5` |

| Final artifact | SHA-256 |
|---|---|
| Frozen `CCA2Scheme.lean` | `c361af28d05eb36cbbfe91d43c0f9b6856d9abf98e7ed4bfaf2e6cff433cb70b` |
| This fourth proposal patch | `6dab03ce654e5fa5fbbb112eec8a9dbb22ca08f16289d23015847cd4546de399` |
| Source after this patch alone | `055ad23371336a9a5973b67bfb47c5378827a335169ee8d594bba65f4d6ed29f` |
| Source after all four in order | `763c982460e54373d89b3bd272eb849133379c6e6104a3c7ad581fb789896443` |

## Coverage of the original completed-seal diagnostics

| Probe line | Frozen source line | Existing local proof | Proposal |
|---|---|---|---|
| 2092 | 320 | `correct.hρ` | `CCA2Scheme-correct-gen-coins-reader.patch` |
| 2094 | 322 | `correct.hr` | `CCA2Scheme-correct-enc-coins-reader.patch` |
| 2104 | 332 | `enc_length.hρ` | `CCA2Scheme-enc-length-gen-coins-reader.patch` |
| 2107 | 335 | `enc_length.hr` | `CCA2Scheme-enc-length-enc-coins-reader.patch` |

**All four original diagnostic sites are addressed by the proposal sequence.** Static checks
confirm all four old `simp; rfl` coin-length proofs are replaced, with exactly four added uses
of each coin-length/coin-polynomial public reader. This is source-level coverage, not a claim
that the module or seal now passes. Native elaboration and the refreshed whole-file seal may
reveal additional diagnostics; root retains application and checking ownership.
