<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.WeightedConstraintExperiment.abs_uniformExpectation_subtype_le_failureProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform expectation difference bound

**Claim.** For a nonempty finite set and a nonempty good subset, if the payoff lies in $[0,1]$, the absolute difference between its uniform mean on the whole set and its uniform mean on the good subset is at most the fraction of elements outside the good subset.

**Proof.** Write $G$ for the good elements and $B$ for the remaining elements, and let $g$ and $b$ be their respective cardinalities. Let $S_G$ and $S_B$ be the sums of the payoff over these two parts. The pointwise bounds on the payoff give $0\le S_G\le g$ and $0\le S_B\le b$, while the total sum is $S_G+S_B$ and the total cardinality is $g+b$. The failure probability is therefore $b/(g+b)$. The difference of the two means can be written as $(gS_B-bS_G)/((g+b)g)$. The bounds on the two sums imply $-bg\le gS_B-bS_G\le bg$, so its absolute value is at most $bg$. Since $g>0$ and $g+b>0$, dividing by the denominator bounds the absolute difference by $b/(g+b)$, as required.
