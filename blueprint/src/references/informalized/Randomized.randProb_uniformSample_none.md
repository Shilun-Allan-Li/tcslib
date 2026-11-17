<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UniformSample.lean :: Randomized.randProb_uniformSample_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of No Accepted Sample

**Claim.** For $N,k\in\mathbb{N}$, if $L=\mathrm{size}(N-1)$, the probability that all $k$ sampled $L$-bit blocks have values at least $N$ is $\left(\frac{2^L-N}{2^L}\right)^k$.

**Proof.** A run returns no value exactly when none of its $k$ block values is less than $N$: the procedure’s list of block values has no entry satisfying the acceptance condition. The probability of this event is therefore the probability that every block satisfies $v\not<N$. The independent-block probability formula (`randProb_forall_blocks`) expresses it as the $k$th power of the probability that one $L$-bit block is rejected. For one block, its value ranges over $0,\ldots,2^L-1$; the probability of rejection is the number of values in that range that are at least $N$, divided by $2^L$ (`randProb_bitsVal`). Those values form the interval from $N$ up to but excluding $2^L$, which has size $2^L-N$. Thus the one-block rejection probability is $(2^L-N)/2^L$, giving the claimed power.

**Key facts.** `Randomized.sampleTries_eq_find`, `Randomized.randProb_forall_blocks`, `Randomized.randProb_bitsVal`.
