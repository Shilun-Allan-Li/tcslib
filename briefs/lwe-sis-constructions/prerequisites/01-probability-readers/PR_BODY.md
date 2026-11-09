Add the two owner-side predicate readers needed to apply the existing strong
leftover-hash theorem in the Regev statistical hybrid on draft #250.

- `TCSlib.InformationTheory.isUniversal_iff` gives the collision count bound.
- `TCSlib.InformationTheory.FinDist.hasMinEntropy_iff` gives the point probability bound.

Both readers use `Iff.rfl` and have no simp attribute. The user approved the two reader formulas. The patch adds one `omit` line to
exclude the unused input-type `Fintype` instance from `isUniversal_iff`. The shared-file overlap is limited to `UniversalHashing.lean`
and `FinDist.lean`. The Lean source is `004bd5b89e48dec52e045bba32439375b82eaead`.
The target is `cryptography/lwe-sis-constructions` at
`27f9ea89b72d84abaec8128f2abd826f24aaced4`.

Gate 11 passes the two readers with zero blockers, majors, and minors. The
auditor independently reproduced the four-module leftover-hash check and
three axiom prints. The landing run also checks the full InformationTheory
facade in a fresh private olean tree, with zero errors, warnings, or admissions.
The three axiom prints use only standard axioms. InformationTheory lint retains
14 inherited failures and two inherited warnings. The `HasMinEntropy` reader
warning resolves.

The exact target merge preview matches the audited reader tree. The
`FinDist.lean` overlaps with the published Pass–Shelat base and #248 combine
cleanly in file-level three-way checks. This PR is the prerequisite for #250's
statistical hybrid. [Gate 11 findings](https://github.com/Shilun-Allan-Li/tcslib/blob/259ff8a13ba08034a15ab7c8464d5ad4a122d6fd/audits/lwe-sis-regev-statistical-proofs-findings.md)

**Clear to merge.** The audited two-reader diff passes the applicable landing
checks. The user approves and merges into the campaign branch.
