<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFTerm.eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of term evaluation

**Claim.** A term evaluates to $-1$ at a sign vector exactly when every literal in it requires the sign present at its coordinate.

**Proof.** By definition, the term evaluates to $-1$ exactly when every literal in its list evaluates to $-1$. A literal evaluates to $-1$ exactly when the sign vector at its coordinate equals its required sign (FABL.Literal.eval_eq_neg_one_iff). Applying this characterization to each literal gives the claimed equivalence.

**Key facts.** `FABL.Literal.eval_eq_neg_one_iff`.
