<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.deterministicRestrictedWeightCost_resource_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restricted-weight resource bounds

**Claim.** For every restricted-weight input, every coordinate set $J$, and every subset $S\subseteq J$, the deterministic restricted-weight cost uses zero random examples, and both its query count and work are at most the input's polynomial budget.

**Proof.** 1. Write $q_i$ and $q_o$ for the inner and outer generator scales, $m_i$ and $m_o$ for the corresponding sample counts, and set $Q=q_i+q_o+1$. Then $Q\ge1$, and each of $q_i,q_o$ and their successors is at most $Q$. The sample-count bound (\texttt{SmallBiasFourierInput.sampleCount_le_four_mul_scale_sq}) gives $m_i\le4q_i^2$ and $m_o\le4q_o^2$, hence both are at most $4Q^2$. Also, the dimension is at most the inner scale by the scale bound (\texttt{SmallBiasInput.n_le_scale}). Since $S\subseteq J\subseteq[n]$, its cardinality is at most $n$, so $|S|\le Q$ and consequently $|S|+2\le3Q$.

2. These estimates bound the local-work expression: first $m_i(|S|+2)+3\le15Q^3$, and then $m_o(m_i(|S|+2)+3)+1\le61Q^8$. For the query count, $m_om_i\le16Q^4\le16Q^8$. The cost-component identities give the query component as the deterministic query count and the work component as construction work plus query count plus local work (\texttt{deterministicRestrictedWeightCost_queries}, \texttt{deterministicRestrictedWeightCost_work}).

3. Each of the two construction costs is bounded using the polynomial bound for deterministic small-bias construction (\texttt{deterministicSmallBiasWork_le_polynomialBudget}): the inner and outer costs are at most $2^{17}(q_i+1)^8$ and $2^{17}(q_o+1)^8$, respectively. Since both scales plus one are at most $Q$, their sum is at most $2^{18}Q^8$. Combining this with the query and local-work bounds gives total work at most $(2^{18}+77)Q^8\le2^{20}Q^8$. The query bound $16Q^8$ is also at most $2^{20}Q^8$. Finally, the cost uses zero random examples by the corresponding component identity (\texttt{deterministicRestrictedWeightCost_randomExamples}). These are exactly the three asserted resource bounds, since the polynomial budget is $2^{20}(Q)^8$.

**Key facts.** `FABL.SmallBiasFourierInput.sampleCount_le_four_mul_scale_sq`, `FABL.SmallBiasInput.n_le_scale`, `FABL.deterministicRestrictedWeightCost_queries`, `FABL.deterministicRestrictedWeightCost_work`, `FABL.deterministicSmallBiasWork_le_polynomialBudget`, `FABL.deterministicRestrictedWeightCost_randomExamples`.
