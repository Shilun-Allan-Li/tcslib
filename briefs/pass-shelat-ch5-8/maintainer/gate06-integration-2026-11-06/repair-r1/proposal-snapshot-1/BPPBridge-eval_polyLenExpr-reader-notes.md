# BPPBridge: polynomial-schedule evaluation proposal

Unapplied patch: `BPPBridge-eval_polyLenExpr-reader.patch`.
Frozen head: `e9d64158461bfe24ddc88ab885bc4017899b4c16`.
No library source edit, Lean/cache/build command, or Git mutation occurred.

## Root and scope

The completed valid V3 pilot is
`evidence-rule10-r2/runs-v3/G06Seal_019_TCSlib_Cryptography_Randomness_BPPBridge_HarnessV3.log`
in the records checkout. It installed/verified 2482 names (2464 active plus
18 already irreducible), reached its EOF verifier, and completed with RC 1.
The first diagnostic, probe 115:59, is source `BPPBridge.lean:65`:
`rfl` no longer identifies `(polyLenExpr a k).eval n` with the foreign ordinary
definition `Randomized.polyLen a k n` under the seal.

This proposal repairs only that existing proof. The separate probe 132:9 / source
82 failure while destructuring `polyTimeModel.Eff` is intentionally untouched.

Frozen source fingerprints:

- `TCSlib/Complexity/Randomized/Classes.lean`:
  `a3ee23e06475fcc0de1022bae605968d1dc38fcbc4f41dc4321eb7c511660b10`.
- `TCSlib/Cryptography/Randomness/BPPBridge.lean`:
  `476f15a4848d40d5ee8fa42b937d9566016940db5912967614e6cdbd5cf27aec`.

## The public API repair

The frozen library has `polyLenExpr_eq`, but no general `polyLen_eq` or
`polyLen_apply` equation. Add the missing reader immediately beside the owning
definition, `Randomized.polyLen` at `Classes.lean:254`:

`polyLen_eq (a k n : Nat) : polyLen a k n = a * (n + 1) ^ k := rfl`.

It has a formula docstring, a term proof in the owning file, and no `simp`
attribute. It adds no algorithm, hypothesis, helper definition, host or
admission. The original `polyLen` definition is unchanged.

Replace only `eval_polyLenExpr`'s proof with one tactic block using:

- its own `polyLenExpr_eq`;
- `PolyExpr.eval_mul`, `eval_const`, `eval_pow`, `eval_add`, `eval_var`;
- the new home reader `Randomized.polyLen_eq`.

Both sides become the same natural-number expression `a * (n + 1) ^ k` for all
`a`, `k`, `n`. No foreign ordinary definition is named in a tactic list or read
through `rfl` in the consumer. The existing public theorem header and its
existing `@[simp]` attribute are preserved.

## Verification and remaining work

The two patch sections match the frozen source. There is exactly one revised
existing proof block; the new owner reader is term `rfl`. Original definitions,
algorithms, public headers and admissions remain unchanged. The complete
`verifier_toNUPPT` block and all later source bytes are unchanged.

No caller needs a statement update. The owning Classes module must be rebuilt
before checking its consumer so that the new reading theorem is available;
the current imports already reach that module and need no change.

The proposal is uncompiled. Root should later check the owner and consumer in
the coordinated native/sealed tree. The independent `polyTimeModel` efficiency
reader/destructuring root remains for a separate invocation; this patch does
not imply that BPPBridge as a whole passes its seal.
