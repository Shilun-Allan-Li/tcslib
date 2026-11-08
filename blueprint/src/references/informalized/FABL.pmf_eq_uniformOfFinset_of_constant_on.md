<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.pmf_eq_uniformOfFinset_of_constant_on -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Constant Masses Give the Uniform Distribution

**Claim.** If a probability mass function on a finite type is supported on a nonempty finite set $S$ and has the same mass at every pair of points in $S$, then it is the uniform probability mass function on $S$.

**Proof.** Choose a point $a_0\in S$. The total mass of the probability mass function is $1$, and it vanishes outside $S$, so the sum of its masses over $S$ is also $1$. By constancy, every summand in this finite sum equals $p(a_0)$; hence $p(a_0)\,|S|=1$ (with the cardinality viewed as an extended nonnegative real). Thus the mass at each point of $S$ is the reciprocal of $|S|$, which is precisely the value of the uniform probability mass function there. Outside $S$, both mass functions vanish. Therefore they agree at every point and are equal.
