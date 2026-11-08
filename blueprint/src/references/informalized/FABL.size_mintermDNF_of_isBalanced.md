<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.size_mintermDNF_of_isBalanced -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Balanced minterm DNF size

**Claim.** If $n$ is positive and the uniform mean of the real-valued sign of $f$ is zero, then the minterm DNF formed from inputs where $f=-1$ has size $2^{n-1}$.

**Proof.** The balancedness hypothesis gives that the uniform probability of the event $f(x)=-1$ is $1/2$ (\(`uniformProbability_neg_one_eq_half_of_isBalanced`\)). Writing this probability as the number of such inputs divided by the size of the cube, and using that the cube has $2^n$ points, shows that the number of inputs with value $-1$ is $2^n/2$. Since $n>0$, this equals $2^{n-1}$. The minterm DNF has one term for each such input, so its size is exactly that number.

**Key facts.** `FABL.uniformProbability_neg_one_eq_half_of_isBalanced`.
