<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Classes.lean :: Randomized.inRP_of_zeroError -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Amplifying a zero-error verifier

**Claim.** Under the stated closure properties, the zero-error partial verifier yields an efficient one-sided randomized verifier for $L'$, with acceptance probability at least $2/3$ on members and certainty of rejection on nonmembers.

**Proof.** Test whether one run of $M$ returns $b$, and take the OR of two such tests on two independent random-tape blocks. The answer-testing closure makes the first test efficient, and the OR closure makes the resulting verifier efficient. Its tape length is twice the original polynomial length, which is again polynomial.

For a member $x$, a run cannot return $!b$; hence every non-aborting run returns $b$. Since the abort probability is at most $1/2$, one run returns $b$ with probability at least $1/2$. The two blocks are independent, so the probability that both tests fail is the square of the one-run failure probability, at most $(1/2)^2=1/4$. Thus the OR accepts with probability at least $3/4$, and in particular at least $2/3$.

For a nonmember, no random tape makes $M$ return $b$. Neither block can therefore pass its test, so the OR rejects on every tape. To apply the hypotheses to each block, observe that each block has exactly the original length; conversely, each such block can be represented by a random tape of that length.

**Key facts.** `Randomized.randProb_mono`, `Randomized.randProb_not`, `Randomized.randProb_congr`, `Randomized.randProb_split`, `Randomized.randProb_take`, `Randomized.exists_ofFn_eq`.
