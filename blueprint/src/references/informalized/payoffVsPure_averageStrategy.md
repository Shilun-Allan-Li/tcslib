<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/LearningTheory/Minimax/HedgeInteraction.lean :: payoffVsPure_averageStrategy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Payoff of the average strategy

**Claim.** Against a fixed pure column, the payoff of the average of the given strategies equals the average of their payoffs against that column.

**Proof.** By definition, the average strategy assigns row $i$ the weight $\bigl(\sum_t p_t(i)\bigr)/T$. Substitute these weights into the payoff sum. For each row, multiplication by its fixed payoff entry distributes over the finite sum over rounds, so the result is $\sum_i\sum_t p_t(i)A_{ij}/T$. Move division by $T$ outside the finite sum over rows, then interchange the two finite sums. The resulting expression is exactly $\bigl(\sum_t\sum_i p_t(i)A_{ij}\bigr)/T$.
