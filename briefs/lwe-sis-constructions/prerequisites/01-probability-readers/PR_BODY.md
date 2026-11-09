Add the two owner-side predicate readers needed to apply the existing strong
leftover-hash theorem in the Regev statistical hybrid on draft #250.

- `TCSlib.InformationTheory.isUniversal_iff` gives the collision count bound.
- `TCSlib.InformationTheory.FinDist.hasMinEntropy_iff` gives the point probability bound.

Both readers use `Iff.rfl` and have no simp attribute. The user approved the two reader formulas. The patch adds one `omit` line to
exclude the unused input-type `Fintype` instance from `isUniversal_iff`. The shared-file overlap is limited to `UniversalHashing.lean`
and `FinDist.lean`. The Lean source is `004bd5b89e48dec52e045bba32439375b82eaead`.
The target is `cryptography/lwe-sis-constructions` at
`27f9ea89b72d84abaec8128f2abd826f24aaced4`.

Fresh serial checks pass for the four-module `LeftoverHash` closure with zero
errors and admissions. Both readers and `leftover_hash` use only standard axioms.
InformationTheory lint retains 14 baseline failures and two baseline warnings.
The `HasMinEntropy` reader warning resolves. The broader facade attempt stopped
at `Entropy` because the isolated cache lacks `NegMulLog`. The scoped result
covers the owner modules and their leftover-hash consumer.

**Not yet clear to merge.** This prerequisite is ready for audit. The user
approves and merges each PR into the campaign branch.
