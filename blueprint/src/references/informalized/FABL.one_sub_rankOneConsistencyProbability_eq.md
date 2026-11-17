<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.one_sub_rankOneConsistencyProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complement of rank-one consistency probability

**Claim.** For $\gamma\in\mathbb F_2^n$ and an $n\times n$ matrix $A$ over $\mathbb F_2$, the probability that $\langle\gamma,x\rangle\langle\gamma,y\rangle$ differs from the matrix pairing on independent uniform $x,y$ is one minus the probability that they are equal.

**Proof.** Rewrite the uniform probability of equality as the expectation over pairs $(x,y)$ of the indicator that the two quantities agree. The expectation over the product space is the iterated expectation over $x$ and then $y$. For each fixed pair, the complement of the equality indicator is exactly the indicator of inequality: it is $0$ when the quantities agree and $1$ otherwise. Taking the iterated expectations gives the stated identity, expressing the matrix pairing on the outer product as the matrix character evaluated there.
