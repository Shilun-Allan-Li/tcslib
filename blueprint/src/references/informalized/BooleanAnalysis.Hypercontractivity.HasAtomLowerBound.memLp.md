<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.HasAtomLowerBound.memLp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Atomic Support Gives Integrability

**Claim.** If a measurable real-valued function lies almost everywhere in a finite set, then it belongs to $L^p$ for every extended nonnegative exponent under a finite measure.

**Proof.** Choose a finite set $s$ containing the values of $X$ almost everywhere. The finite sum $M=\sum_{x\in s}|x|$ bounds the absolute value of every element of $s$, since each summand is nonnegative and includes the corresponding $|x|$. Thus $|X|\le M$ almost everywhere. Measurability gives strong measurability, and the finite-measure boundedness criterion for $L^p$ (`MemLp.of_bound`) then implies $X\in L^p(\mu)$ for every extended nonnegative exponent. The lower bound on the masses of the atoms is not needed for this implication.
