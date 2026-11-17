<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.uniformProbability_bool_false_add_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complementary Boolean probabilities

**Claim.** For a Boolean-valued function on $\operatorname{Fin}(n)$, the uniform probabilities of the values false and true sum to $1$.

**Proof.** At each coordinate exactly one of the two values is false or true. Thus the two event indicators add to the constant function $1$. Averaging this identity over all $n$ coordinates gives the sum of the two uniform probabilities as the average of $1$, which is $1$.
