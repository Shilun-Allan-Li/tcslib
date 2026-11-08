<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LowDegreeSpectralConcentration.lean :: FABL.relevantCoordinates_toReal_eq_empty_of_fourierDegree_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No Relevant Coordinates at Degree Zero

**Claim.** If a sign-valued Boolean function has Fourier degree zero, then its set of relevant coordinates is empty.

**Proof.** Suppose a coordinate $i$ were relevant. By the definition of relevance, its influence is positive; membership in the relevant-coordinate set expresses exactly this condition (\texttt{mem\_relevantCoordinates}). Each coordinate's influence is nonnegative (\texttt{influence\_nonneg}), so the influence at $i$ is at most the sum of all coordinate influences, the total influence. The total influence of a sign-valued function is bounded above by its Fourier degree (\texttt{totalInfluence\_toReal\_le\_fourierDegree}). Under the degree-zero hypothesis, this makes the total influence at most zero, contradicting the positive influence at $i$. No coordinate can therefore belong to the relevant-coordinate set, so that set is empty.

**Key facts.** `FABL.mem_relevantCoordinates`, `FABL.influence_nonneg`, `FABL.totalInfluence_toReal_le_fourierDegree`.
