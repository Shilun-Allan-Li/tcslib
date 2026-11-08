<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/PolyHierarchy/Levels.lean :: Complexity.P_subset_PH -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time in the Polynomial Hierarchy

**Claim.** Every language in polynomial time belongs to the polynomial hierarchy: $\mathsf{P} \subseteq \mathsf{PH}$.

**Proof.** The zeroth existential level is exactly polynomial time (\(\texttt{Complexity.SigmaP\_zero}\)). Every existential level is contained in the polynomial hierarchy (\(\texttt{Complexity.SigmaP\_subset\_PH}\)); in particular, this holds at level zero. Substituting the equality of that level with $\mathsf{P}$ proves the inclusion.

**Key facts.** `Complexity.SigmaP_zero`, `Complexity.SigmaP_subset_PH`.
