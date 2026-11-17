<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomBits.lean :: Randomized.randProb_append_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound for Appended Events

**Claim.** Under the stated hypotheses, the probability that a uniformly random string of length $m_1+m_2$ has its first part and remaining part satisfy $C$ is at most $P_{m_1}(A)\varepsilon$.

**Proof.** Apply the lower bound for appended-event probabilities (`Randomized.randProb_append_ge`) to the event that the first part satisfies $A$ and the second part fails $C$. For every first part satisfying $A$, the assumed upper bound on the probability of $C$ implies that the probability of its complement is at least $1-\varepsilon$. Thus the probability of this joint event is at least $P_{m_1}(A)(1-\varepsilon)$. The same lower-bound result applied to the event that the first part fails $A$, with no restriction on the second part, shows that the probability the first part fails $A$ in a full string is at least $1-P_{m_1}(A)$. Here the unrestricted second part has probability one (`Randomized.randProb_true`).

Partition strings for which $C$ fails into two disjoint cases: the first part satisfies $A$ and $C$ fails, or the first part fails $A$. The containment hypothesis $C(u,v)\Rightarrow A(u)$ ensures this is exhaustive. By additivity for disjoint events (`Randomized.randProb_or_disjoint`), the probability that $C$ fails is the sum of the probabilities of these two cases. Combining the lower bounds gives a failure probability of at least $P_{m_1}(A)(1-\varepsilon)+1-P_{m_1}(A)=1-P_{m_1}(A)\varepsilon$. Finally, complementary events have probabilities summing to one (`Randomized.randProb_not`), so the probability of $C$ is at most $P_{m_1}(A)\varepsilon$. The proof identifies predicates on length-indexed Boolean functions with their corresponding list predicates when applying these probability facts (`Randomized.randProb_congr`).

**Key facts.** `Randomized.randProb_append_ge`, `Randomized.randProb_congr`, `Randomized.randProb_not`, `Randomized.randProb_or_disjoint`, `Randomized.randProb_true`.
