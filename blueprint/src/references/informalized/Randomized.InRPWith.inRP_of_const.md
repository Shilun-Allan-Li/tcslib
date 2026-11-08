<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RPExpected.lean :: Randomized.InRPWith.inRP_of_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Acceptance Amplification

**Claim.** If an efficient verifier accepts members with probability at least $\rho$, rejects nonmembers with certainty, and $(1-\rho)^K\le 1/3$, then repeating it independently $K$ times and accepting if any run accepts yields acceptance probability at least $2/3$ on members and perfect rejection on nonmembers.

**Proof.** Let $M$ be the original verifier, with random-bit bound $q=a(|x|+1)^k$. Use the verifier that divides a random string into $K$ consecutive blocks of $q$ bits, runs $M$ on each block, and accepts if any run accepts. Its random-bit bound is $Kq$, which is the polynomial bound with coefficient $Ka$ and the same degree; closure of the verifier model under this repeated-any construction gives efficiency (\texttt{polyTimeModel\_closedUnderAny}).

Fix a member $x$, and write $s$ for the acceptance probability of one run. The probability that none of the $K$ independent blocks accepts is $(1-s)^K$: this is the zero-success case of the block-count formula (\texttt{randProb\_blockCount}), together with the complement rule for probabilities (\texttt{randProb\_not}). Since $s\ge\rho$ and $s\le1$ (\texttt{randProb\_le\_one}), we have $0\le1-s\le1-\rho$, hence $(1-s)^K\le(1-\rho)^K\le1/3$. Therefore the repeated verifier accepts with probability $1-(1-s)^K\ge2/3$.

Now let $x$ be a nonmember and consider any random string of length $Kq$. Each block has length $q$; the block-count partition of the string identifies each such block with a $q$-bit random string. Perfect rejection of nonmembers by $M$ makes every block reject. Thus none accepts, and the repeated verifier rejects on every random string.

**Key facts.** `Randomized.polyTimeModel_closedUnderAny`, `Randomized.randProb_blockCount`, `Randomized.randProb_not`, `Randomized.randProb_le_one`.
