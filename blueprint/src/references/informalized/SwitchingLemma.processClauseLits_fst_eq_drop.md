<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: processClauseLits_fst_eq_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The remaining path is a suffix of the input path

**Claim.** `(processClauseLits lits path ρ₀ σ).1 = path.drop (min lits.length path.length)`.
The path component returned by `processClauseLits` is literally the input path
with its first `min lits.length path.length` entries removed — one entry consumed
per processed literal, stopping when either list runs out.

**Proof.** Two-line induction.

1. `induction' lits with hd tl hl generalizing path ρ₀ σ`.
2. Base case: `cases path <;> aesop` — with no literals nothing is dropped.
3. Cons case: `cases path <;> simp_all +decide [processClauseLits]`; the empty
   path returns `[]`, and one step peels a `List.drop` off both sides so the
   induction hypothesis closes it.

**Used in.** `canonicalPath_preserve_processClauseLits` (`hrem`), where the
remaining path must be recognised as a suffix of the canonical decision-tree
path before its length can be bounded by the depth of the tree at the updated
restriction.
