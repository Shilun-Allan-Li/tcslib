<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/polylogIndep.lean :: Circuit.prob_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability Is at Most One

**Claim.** For a circuit $C$ and a probability mass function $\mu$ on Boolean assignments, the probability that $C$ evaluates to true under $\mu$ is at most $1$.

**Proof.** For each assignment $x$, the summand defining the probability is either $(\mu(x)).\mathrm{toReal}$ or $0$, and in either case it is at most $(\mu(x)).\mathrm{toReal}$, since the latter is nonnegative. Summing these pointwise inequalities bounds the circuit probability by the sum of the real-valued masses of all assignments. The total mass of a probability mass function is $1$; converting its total mass from extended nonnegative reals to reals gives that this sum is $1$.
