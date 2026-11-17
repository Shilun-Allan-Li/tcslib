<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/ChoiceWords.lean :: Turing.expCertificateLength_strictMono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict increase of an exponential expression

**Claim.** For natural numbers $C$ and $c$, the function $n\mapsto n+C\,2^{(n+1)^c}$ is strictly increasing.

**Proof.** Let $n<m$. The first summand increases strictly: $n<m$. Also $n+1\le m+1$, so raising these positive natural numbers to the power $c$ preserves the weak inequality, and raising $2$ to those exponents does as well. Multiplication by the nonnegative number $C$ preserves that weak inequality. Adding the two summand inequalities, with the first strict, shows $n+C2^{(n+1)^c}<m+C2^{(m+1)^c}$.
