<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalTermIndex_eq_of_extends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Canonical Index Under Extension

**Claim.** If $\eta$ extends $\rho$, both restrictions admit compatible terms, and the term of least index compatible with $\rho$ is also compatible with $\eta$, then the least compatible indices for $\eta$ and $\rho$ are equal.

**Proof.** Let $i_\rho$ and $i_\eta$ be the least compatible indices for the two restrictions. Since the term at $i_\rho$ is compatible with $\eta$, this index belongs to the set of indices compatible with $\eta$. Its minimum therefore satisfies $i_\eta\le i_\rho$. Conversely, the term at $i_\eta$ is compatible with $\eta$ by the defining property of a minimum in a nonempty finite set. Compatibility is preserved when passing from an extending restriction to the restriction it extends (`DNFTerm.compatible_of_extends`), so this term is compatible with $\rho$. Thus $i_\rho\le i_\eta$. The two inequalities give equality.

**Key facts.** `FABL.DNFTerm.compatible_of_extends`.
