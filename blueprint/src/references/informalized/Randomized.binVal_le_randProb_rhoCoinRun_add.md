<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.binVal_le_randProb_rhoCoinRun_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value and Finite Coin-Run Probability

**Claim.** For an infinite Boolean sequence and any $K$, its binary value is at most the probability that the length-$K$ coin run returns true, plus $2^{-K}$.

**Proof.** The finite coin-run probability is the sum of the first $K$ binary weights whose digits are true (\texttt{Randomized.randProb_rhoCoinRun_eq_sum_real}). Split the infinite series defining the binary value into those first $K$ terms and its tail; summability of the binary-weight series justifies this decomposition (\texttt{Randomized.summable_binVal}). The finite part is exactly the stated probability. For the tail, reindex beyond $K$ and bound each digit indicator by $1$. The tail is therefore at most $\sum_{i\ge0}2^{-K}(1/2)2^{-i}$, which equals $2^{-K}$ by the geometric-series formula. Adding the finite part and this tail bound proves the inequality.

**Key facts.** `Randomized.randProb_rhoCoinRun_eq_sum_real`, `Randomized.summable_binVal`.
