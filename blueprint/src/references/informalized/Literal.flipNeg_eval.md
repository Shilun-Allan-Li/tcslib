<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: Literal.flipNeg_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Flipping a literal negates its value

**Claim.** For every literal `l : Literal n` and every input `x : Fin n → Bool`,
`l.flipNeg.eval x = !(l.eval x)`.

**Proof.** A two-case unfolding.

1. `simp only [Literal.flipNeg, Literal.eval]` replaces `l.flipNeg` by
   `⟨l.var, !l.neg⟩` and expands `Literal.eval` into its
   `if l.neg then !x l.var else x l.var` form.
2. `cases l.neg <;> simp` settles both polarities: for a positive literal the
   claim is `!x l.var = !(x l.var)`, and for a negated literal it is
   `x l.var = !(!x l.var)`.

Granular `@[simp]` helper for the De Morgan dual construction.

**Used in.** `cnfToDualDNF_eval` (`(cnfToDualDNF ψ).eval x = !(ψ.eval x)`), in the
inner induction over the literals of a single clause.
