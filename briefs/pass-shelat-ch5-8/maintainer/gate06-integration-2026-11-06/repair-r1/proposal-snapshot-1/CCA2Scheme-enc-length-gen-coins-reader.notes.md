# CCA2Scheme: ciphertext-length generator coin proof proposal

**UNAPPLIED; native elaboration and sealed replay pending.** Frozen head supplied by root:
`e9d64158461bfe24ddc88ab885bc4017899b4c16`. The current library source retains its frozen
SHA-256. No library edit, Lean/cache command, Git command, or app was used here.

Only the local generator-length `hρ` proof in `ccaScheme.enc_length`, at frozen source
line **332**, changes. This maps to completed seal diagnostic probe line **2104**. Its
`rfl` attempts to read sealed `NUPPT.coinLen` and uniform-machine constructor bodies.
The proposed `rw` chain uses six public theorems: `List.length_ofFn`, `NUPPT.coinLen_eq`,
`NUPPT.coins_ofPolyTimeUniform`, and `PolyExpr.eval_mul`/`eval_const`/`eval_var`.
The local `ccaGen` abbreviation only expands to match the published constructor equation.

Exactly one existing tactic block changes. Definitions, data fields, public headers,
admissions and every other proof block remain unchanged. No helper or admission is added.
The local encryptor-length proof at frozen line **335** remains byte-for-byte unchanged,
both in this standalone proposal and after all three proposals in the sequence below.

## Application order and static composition

1. `CCA2Scheme-correct-gen-coins-reader.patch` (frozen line 320).
2. `CCA2Scheme-correct-enc-coins-reader.patch` (frozen line 322).
3. `CCA2Scheme-enc-length-gen-coins-reader.patch` (this frozen line 332).

Exact-context in-memory application passed for this patch alone and after the first two
proposals. The two preceding proposals shift this target to line 336 before step 3.
Only static context/byte checks were run; this is not a Lean or seal result.

| Artifact | SHA-256 |
|---|---|
| Frozen `CCA2Scheme.lean` | `c361af28d05eb36cbbfe91d43c0f9b6856d9abf98e7ed4bfaf2e6cff433cb70b` |
| First proposal patch | `ac644eb1ed3d76b21090cc1b3b523c9c1c0c72336b86a7be93e5fc92eb82118e` |
| Second proposal patch | `495d121f73ea23071af855ffdb2cb65b83ae50d670a81d770e919e2b370f0ce1` |
| This third proposal patch | `c09a9240c7d4686d80fe5815de6909be4e32767df536d7b87cca2ee55ef9c0fe` |
| Source after this patch alone | `a4d7ee642c495b64e7c43bff66a980bb267262d797cb6e9a41bb07429b2f0157` |
| Source after first two proposals | `92d253838b287d5bfcfa73165cd088cb2da2666395de0344f05700854ab247c6` |
| Source after all three in order | `c0997797cf9f736aadb3c423be31ca9b3950ce8292df6f885e328d4741c016e5` |

Root retains patch application and native checking ownership. The source-line-335 diagnostic
is deliberately left for the next invocation; this proposal makes no claim that CCA2Scheme
passes its whole-file seal after application.
