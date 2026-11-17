<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Formulas.lean :: DNF.width_mk -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width of a Constructed DNF

**Claim.** The width of the DNF with terms $ts$ is the maximum number of literals in any term of $ts$, taking the maximum to be $0$ when $ts$ is empty.

**Proof.** Unfolding the width of the constructed formula gives the width of its list of terms, which is defined as the fold of the term lengths using maximum, starting from $0$. This is exactly the stated maximum, including the empty-list convention.
