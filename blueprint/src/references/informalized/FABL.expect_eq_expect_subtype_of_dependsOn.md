<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.expect_eq_expect_subtype_of_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation on Relevant Coordinates

**Claim.** If a function on assignments over a finite set depends only on coordinates in $D$, its uniform average over all assignments equals its average over assignments on $D$, extended by a fixed element of the nonempty value set outside $D$.

**Proof.** Split each assignment on $E$ into its restrictions to $D$ and to the complement of $D$. This is a bijection between assignments on $E$ and pairs of assignments on those two parts, so the uniform average becomes an iterated average over the pair. For fixed values on $D$, changing the values on the complement does not change the function, by the hypothesis that it depends only on $D$. Thus the inner average over complement assignments is constant and equals the value obtained by filling every outside coordinate with a fixed element of $\Omega$. Averaging over the inside assignments alone gives the stated equality.
