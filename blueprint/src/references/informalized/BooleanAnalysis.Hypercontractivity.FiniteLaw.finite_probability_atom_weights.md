<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/FiniteLaw.lean :: BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_probability_atom_weights -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weights of finite-law atoms

**Claim.** For a probability measure and a measurable random variable supported almost everywhere on a finite set, the real masses of the atoms indexed by that set sum to one. If each atom has measure at least the nonnegative number $\lambda$, then each real atom weight is also at least $\lambda$.

**Proof.** Apply the finite-law integral formula (`BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_integral`) to the constant function $1$. Its integral is $1$ because the measure is a probability measure, and each summand is the real mass of the corresponding atom. This proves that the atom weights sum to one. For each $x\in s$, the assumed lower bound compares the extended-real atom measure with $\lambda$. Both can be converted to real numbers: the atom measure is finite, and the real number $\lambda$ is nonnegative. Monotonicity of the conversion to real numbers therefore gives the claimed lower bound on each real weight.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteLaw.finite_law_integral`.
