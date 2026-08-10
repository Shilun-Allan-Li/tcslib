<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: Literal.flipNeg_var -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Flipping a literal's polarity keeps its variable

**Claim.** For every literal `l : Literal n`, `l.flipNeg.var = l.var`.

**Proof.** Immediate from the definition: `Literal.flipNeg l = ⟨l.var, !l.neg⟩`,
so the `var` field is unchanged and the goal closes by `rfl`.

This is a granular `@[simp]` helper, not a mathematical statement in its own
right.

**Used in.** `cnfToDualDNF_inj`, where it converts a variable-equality
hypothesis about dual (negated) literals back into one about the original
clause's literals.
