<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.one_div_two_mul_q_le_inv_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reciprocal Candidate-Count Bound

**Claim.** For a nonempty finite candidate set whose cardinality is at most $2q$, the reciprocal of $2q$ is at most the reciprocal of the set’s cardinality.

**Proof.** Nonemptiness makes the candidate set’s cardinality positive. Since that cardinality is at most $2q$, taking reciprocals reverses the inequality between these positive quantities, yielding $1/(2q)\le 1/|C|$.
