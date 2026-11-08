<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.InZPP.restart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restarting a Zero-Error Verifier

**Claim.** A zero-error verifier that halts with probability at least $1/2$ can be restarted on fresh blocks so that the total sum of nonhalting probabilities through any finite number of time bounds is at most twice the block length, while every returned value is correct.

**Proof.** Take a verifier $M$ witnessing zero-error randomized recognition, with random-bit bound $N=a(|x|+1)^k$. For each input $x$, define one restarted attempt to run $M$ on the first $N$ bits of its block, and set the block length to $t=N+1$. The unused final bit ensures that the block has positive length; the halting probability for the attempt is still at least $1/2$, because truncating a uniformly random $t$-bit string to its first $N$ bits preserves the distribution on $N$-bit strings (\texttt{randProb\_take}).

The bound for repeated runs says that if a single block has positive length and its nonhalting probability is at most $1/2$, then the sum of the nonhalting probabilities over the first $K$ time bounds is at most $2t$ for every $K$ (\texttt{expTimeLe\_repeatRun}). Applying it to these attempts gives the required bound $2(N+1)$.

Finally, suppose the restarted procedure returns $b$ on some string $w$. A returned value must come from one particular block: there is a block $u$ of length $t$ on which the original run returns $b$ (\texttt{exists\_of\_repeatRun\_eq\_some}). The first $N$ bits of $u$ have length $N$, so they can be represented as the random bits of a run of $M$ (\texttt{exists\_ofFn\_eq}). If $x$ is a member, the zero-error condition rules out the value false; if $x$ is a nonmember, it rules out true. Hence every value returned by restarting is true exactly for members.

**Key facts.** `Randomized.expTimeLe_repeatRun`, `Randomized.randProb_take`, `Randomized.exists_of_repeatRun_eq_some`, `Randomized.exists_ofFn_eq`.
