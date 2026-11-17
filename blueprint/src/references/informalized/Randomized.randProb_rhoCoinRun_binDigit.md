<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.randProb_rhoCoinRun_binDigit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Coin-Run Probability

**Claim.** For $\rho<1$ and any nonnegative integer $K$, the probability that the specified finite coin-run returns true is $\lfloor 2^K\rho\rfloor/2^K$.

**Proof.** The probability of a true return can be written as a sum over positions: position $i$ contributes $2^{-(i+1)}$ precisely when the prescribed bit at that position is true. This is the finite coin-run probability formula (`Randomized.randProb_rhoCoinRun_eq_sum_real`). For the bit sequence defined by the parity of the successive floors of $2^{i+1}\rho$, the weighted sum of its true bits is $\lfloor 2^K\rho\rfloor/2^K$ (`Randomized.sum_binDigit`). Substituting this identity into the probability formula yields the claim.

**Key facts.** `Randomized.randProb_rhoCoinRun_eq_sum_real`, `Randomized.sum_binDigit`.
