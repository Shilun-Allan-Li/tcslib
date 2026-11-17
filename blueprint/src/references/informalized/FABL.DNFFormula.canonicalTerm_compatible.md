<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.canonicalTerm_compatible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Compatibility of the Canonical Term

**Claim.** If at least one term of $\phi$ is compatible with $\rho$, then the term at the least compatible index is compatible with $\rho$.

**Proof.** The canonical index is the minimum of the nonempty finite set of indices whose terms are compatible with $\rho$. A minimum of a nonempty finite set belongs to that set, so the term at this index satisfies the compatibility condition defining membership in the set.
