<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/ThresholdCircuits.lean :: FABL.completeQuadraticPolarFrequency_eq_zero_of_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Polar Frequency Map

**Claim.** When $n$ is even, if every coordinate of the polar frequency of $z$ is zero, then $z=0$.

**Proof.** Let $T=\sum_i z_i$. For each coordinate $i$, the hypothesis says that the sum over all coordinates other than $i$ is zero. Splitting the total sum into the term at $i$ and its complement therefore gives $T=z_i$. Hence every coordinate equals $T$, and summing these equalities yields $T=nT$. Write $n=2k$, since $n$ is even. In characteristic two, $nT=(k+k)T=kT+kT=0$, so $T=0$. Consequently every coordinate $z_i=T$ is zero, and therefore $z=0$.
