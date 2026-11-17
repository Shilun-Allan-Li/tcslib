<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean :: Matrix.rank_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subadditivity of rank over finite sums

**Claim.** For a finite set $s$ and a family of real matrices $(A_i)_{i\in s}$ with a finite column index set, the rank of their sum is at most the sum of their ranks.

**Proof.** Proceed by induction on the finite set $s$. For the empty set, the sum is the zero matrix, whose rank is zero, so the inequality holds. For the induction step, write a nonempty set as the insertion of an element $i$ into a smaller set $s$, where $i\notin s$. The sum over the enlarged set is $A_i+\sum_{j\in s}A_j$. By subadditivity for two matrices (`Matrix.rank_add_le`), its rank is at most $\operatorname{rank}(A_i)+\operatorname{rank}(\sum_{j\in s}A_j)$. The induction hypothesis bounds the latter rank by $\sum_{j\in s}\operatorname{rank}(A_j)$, giving the desired inequality after combining the two terms.

**Key facts.** `Matrix.rank_add_le`.
