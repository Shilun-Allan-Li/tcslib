<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/Depth3Switching.lean :: dtDepth_le_implies_nice_dnf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Shallow decision-tree depth gives a nice narrow DNF

**Claim.** If `f : (Fin n → Bool) → Bool` has `dtDepth f ≤ d`, then there is
`φ : DNF n` with `DNF.width φ ≤ d`, `DNF.eval φ x = f x` for all `x`, every
term `Nodup`, and every term variable-injective (`l₁, l₂ ∈ t` with
`l₁.var = l₂.var` implies `l₁ = l₂`). This is the DNF mirror of
`dtDepth_le_implies_nice_cnf`.

**Proof.** **Not proved.** The body is `sorry`, with the in-file note that it
"needs `dtDepth_neg` and CNF↔DNF negation duality" — i.e. the intended argument
is to apply the CNF version to `!f` and dualise, but neither the `dtDepth`
invariance under negation nor the clause-level cleanup transport is available
yet.

**Note.** The unconditional `dtDepth_le_implies_small_dnf_cnf` (in
`BooleanAnalysis/Switching.lean`) already yields the width and evaluation parts;
only the two term-hygiene conditions are missing. Nothing in the library
currently consumes this declaration, so the `sorry` does not propagate — the
depth-3 chain in this file goes through the CNF side only.
