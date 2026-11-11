<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Coins.lean :: Randomized.binVal_binDigit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Expansion from Floor Digits

**Claim.** For $0\le\rho<1$, the binary value of the sequence whose $i$th digit records the parity of $\lfloor 2^{i+1}\rho\rfloor$ equals $\rho$.

**Proof.** Prove both inequalities by approximating the infinite binary value with the finite coin-run probabilities. Given any $\varepsilon>0$, choose $K$ so that $2^{-K}<\varepsilon$. The finite probability for the digit sequence is exactly $\lfloor 2^K\rho\rfloor/2^K$ (\texttt{Randomized.randProb_rhoCoinRun_binDigit}). The binary value is at most this probability plus $2^{-K}$ (\texttt{Randomized.binVal_le_randProb_rhoCoinRun_add}); and the floor property gives $\lfloor 2^K\rho\rfloor/2^K\le\rho$. Hence the binary value is below $\rho+\varepsilon$, for every positive $\varepsilon$, proving it is at most $\rho$. For the reverse inequality, the finite probability is at most the binary value (\texttt{Randomized.randProb_rhoCoinRun_le_binVal}). The strict floor bound gives $\rho<\lfloor 2^K\rho\rfloor/2^K+2^{-K}$, so $he finite probability is below the binary value and the error term is smaller than $\varepsilon$, giving $\rho<\operatorname{binVal}+\varepsilon$. Since this holds for every positive $\varepsilon$, $\rho\le\operatorname{binVal}$. Together the inequalities yield equality.

**Key facts.** `Randomized.binVal_le_randProb_rhoCoinRun_add`, `Randomized.randProb_rhoCoinRun_binDigit`, `Randomized.randProb_rhoCoinRun_le_binVal`.
