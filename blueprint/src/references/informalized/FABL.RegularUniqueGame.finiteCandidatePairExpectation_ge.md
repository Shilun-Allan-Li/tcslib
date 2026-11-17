<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.finiteCandidatePairExpectation_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paired Candidate Expectation Bound

**Claim.** If $a$ belongs to the finite set $A$, $b$ belongs to the finite set $B$, and $R(a,b)$ holds, then the iterated finite candidate expectation of the indicator of $R$ is at least $1/(|A||B|)$.

**Proof.** The memberships ensure both candidate sets are nonempty, so both expectations are uniform averages. Fix the outer candidate $a$. In the inner sum over $B$, the term at $b$ is $1$, and every other term is nonnegative. Thus the inner average at $a$ is at least $1/|B|$. Every inner average, for any outer candidate, is nonnegative; consequently the sum of these averages over $A$ is at least its term at $a$, hence at least $1/|B|$. Dividing by $|A|$ gives the claimed bound. Nonnegativity of each inner expectation, including the values summed over $A$, follows from nonnegativity of the indicator and the finite candidate expectation lemma (FABL.RegularUniqueGame.finiteCandidateExpectation_nonneg).

**Key facts.** `FABL.RegularUniqueGame.finiteCandidateExpectation_nonneg`.
