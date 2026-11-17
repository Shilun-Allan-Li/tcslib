<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauEmitterInstr.lean :: Complexity.UTab.ok_psnS -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of past-position sources

**Claim.** If $t_0$ being false implies $1\leq\rho(r_{LB})$, then every source in the past-position list is valid for $\rho$.

**Proof.** A source in the list is obtained from some index in the range from $0$ to $W-1$. If $t_0$ is false, it is the corresponding past-position source, whose validity requires $1\leq\rho(r_{LB})$, supplied by the hypothesis. If $t_0$ is true, it is constant false and is valid by definition.
