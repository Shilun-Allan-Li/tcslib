<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/FourierFormulas.lean :: FABL.noiseOperator_eq_sum_degreePart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Noise Operator by Degree

**Claim.** The noise operator is the sum, over degrees $k$ from zero through $n$, of $\rho^k$ times the degree-$k$ part of the function.

**Proof.** The Fourier expansion of the noise operator writes its value at $x$ as a sum over all subsets $S$, with summand $\rho^{|S|}\widehat f(S)\chi_S(x)$ (`noiseOperator_fourier_expansion`). Partition these subsets according to their cardinality $k$. Since every subset of $[n]$ has size at most $n$, the resulting degree index ranges from $0$ to $n$. For each fixed $k$, the factor $\rho^{|S|}$ is $\rho^k$ on that fiber, and the remaining sum is precisely the degree-$k$ part evaluated at $x$.

**Key facts.** `FABL.noiseOperator_fourier_expansion`.
