<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.P_subset_PSPACE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Time Uses Polynomial Space

**Claim.** Every language decidable in polynomial time is decidable using polynomial space, so $\mathsf{P} \subseteq \mathsf{PSPACE}$.

**Proof.** Write $\mathsf{P}$ and $\mathsf{PSPACE}$ as unions over exponents of their respective time and space classes. For each exponent, a language decidable within the corresponding time bound is also decidable within the same space bound (\(\texttt{Complexity.DTIME\_subset\_SPACE}\)). Applying this inclusion at every exponent and taking the unions gives $\mathsf{P} \subseteq \mathsf{PSPACE}$.

**Key facts.** `Complexity.DTIME_subset_SPACE`.
