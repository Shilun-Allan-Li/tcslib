<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Discrete.lean :: BooleanAnalysis.Hypercontractivity.sharp_discrete_hypercontractive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp hypercontractivity for finite laws

**Claim.** Under the stated probability, mean-zero, finite-support, and atom-mass hypotheses, both asserted hypercontractive inequalities hold at the radius $\rho=\sqrt{\sinh(u/q)/\sinh(u/(q/(q-1)))}$, with $u=\log((1-\lambda)/\lambda)$.

**Proof.** The finite-law sharp forward theorem gives the first assertion directly: the function is hypercontractive from exponent $2$ to exponent $q$ at the stated radius (\texttt{SharpDiscrete.finite_law_sharp_forward}). The mean-zero assumption then permits the conjugation principle for hypercontractivity, which converts this forward assertion into the second assertion, from exponent $q/(q-1)$ to exponent $2$ at the same radius (\texttt{IsHypercontractive.conjugate}). Pairing these two conclusions proves the result.

**Key facts.** `BooleanAnalysis.Hypercontractivity.SharpDiscrete.finite_law_sharp_forward`, `BooleanAnalysis.Hypercontractivity.IsHypercontractive.conjugate`.
