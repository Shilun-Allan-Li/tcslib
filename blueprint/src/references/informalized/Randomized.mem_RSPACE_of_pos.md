<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.mem_RSPACE_of_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Acceptance Probability and Space

**Claim.** Under the stated halting, one-sided error, positive acceptance probability, and space hypotheses, the language belongs to $\mathrm{RSPACE}(s)$.

**Proof.** Apply the amplification result for positive acceptance probability (`exists_rDecides_of_pos`) with error parameter $\varepsilon=1/3$. It supplies a finite nondeterministic machine whose space is at most a constant multiple of the original space bound and whose acceptance probability on members is at least $1-1/3=2/3$; rejection on nonmembers remains certain, and every branch halts within the supplied input-dependent bound. Since the original space bound is $c s(n)$, the amplified machine uses at most $a c s(n)$ space for some natural number $a$. Thus it witnesses membership in $\mathrm{RSPACE}(s)$, with constant factor $ac$. The final acceptance inequality follows from $\delta\leq 2/3$ after amplification and the original lower bound $\delta$ where needed in the amplified guarantee.

**Key facts.** `Randomized.exists_rDecides_of_pos`, `Turing.FinNDTM.UsesSpace.mono`.
