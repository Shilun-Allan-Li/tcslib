<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.length_filter_lt_succ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Partitioning a threshold filter

**Claim.** The number of entries of $l$ for which $t(a)<z+1$ is the sum of the number for which $t(a)<z$ and the number for which $t(a)=z$.

**Proof.** Count the entries satisfying each condition by counting their predicates along the list. Induct on the list. The empty list contributes zero to all three counts. For a list beginning with $a$, the induction hypothesis handles the tail, so it remains to check the contribution from $a$. Since $t(a)$ is a natural number, the condition $t(a)<z+1$ holds exactly when either $t(a)<z$ or $t(a)=z$, and these alternatives are disjoint. Hence the contribution on the left is the sum of the two contributions on the right.
