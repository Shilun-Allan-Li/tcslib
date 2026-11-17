<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.prob_exists_not_dvd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Nondividing Block with High Probability

**Claim.** Under the stated bounds on $M$ and $y$, a uniformly chosen bit string of length $16M^2$ has probability at least $3/4$ of containing a block whose represented value plus one does not divide $y$.

**Proof.** A single uniformly chosen block of length $2M$ fails to give a divisor with probability at least $1/(4M)$, by the fingerprint bound. Therefore its probability $q$ of giving a divisor is at most $1-1/(4M)$. The block decomposition identity says that the probability all $8M$ blocks give divisors is $q^{8M}$. Since $(4M)(1/(4M))=1$ and $8M\ge 2(4M)$, the elementary power estimate bounds $(1-1/(4M))^{8M}$ by $(1/2)^2=1/4$. Thus the probability that at least one block fails to give a divisor, the complementary event, is at least $3/4$.

**Key facts.** `Randomized.randProb_forall_blocks`, `Randomized.randProb_not`, `Randomized.fingerprint`, `Randomized.one_sub_pow_le_half_pow`, `Randomized.randProb_nonneg`.
