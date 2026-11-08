<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.binVal_const_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of the All-Ones Sequence

**Claim.** The binary value of the sequence whose every digit is true is $1$.

**Proof.** Every summand in the binary value is $2^{-(i+1)}$. Rewrite this as $(1/2)2^{-i}$; the resulting series is the geometric series with first factor $1/2$ and ratio $1/2$, whose sum is $1$ (the geometric-series identity \texttt{tsum_geometric_two'}).
