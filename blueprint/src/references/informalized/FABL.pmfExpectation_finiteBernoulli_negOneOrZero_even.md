<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/Reasonableness.lean :: FABL.pmfExpectation_finiteBernoulli_negOneOrZero_even -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even moments of a Bernoulli variable

**Claim.** For a Bernoulli bit that equals $1$ with probability $q\in[0,1]$ and $0$ with probability $1-q$, the expectation of the $(2m+2)$-nd power of the variable that is $0$ at bit $1$ and $-1$ at bit $0$ is $1-q$.

**Proof.** At bit $0$, the variable is $-1$, whose even power $2m+2$ is $1$; at bit $1$, it is $0$, whose positive power is $0$. Hence this power is pointwise $1$ minus the bit itself. Linearity of expectation therefore gives its expectation as the expectation of the constant $1$ minus the expectation of the bit. The constant has expectation $1$, and the positive-power Bernoulli moment formula gives expectation $q$ for the bit, so the result is $1-q$.

**Key facts.** `FABL.pmfExpectation_sub`, `FABL.pmfExpectation_const_one`, `FABL.pmfExpectation_finiteBernoulli_zeroOne_pow`.
