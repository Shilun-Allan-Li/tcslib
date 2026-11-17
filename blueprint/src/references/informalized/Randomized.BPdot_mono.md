<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPOperator.lean :: Randomized.BPdot_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of randomized reductions

**Claim.** If $\mathcal C\subseteq\mathcal D$, every language reducing to some language in $\mathcal C$ also reduces to some language in $\mathcal D$.

**Proof.** A language in the reduction closure of $\mathcal C$ comes with a target language $C\in\mathcal C$ and a reduction to $C$. The assumed inclusion puts that same target in $\mathcal D$, while the reduction is unchanged. Thus the language belongs to the reduction closure of $\mathcal D$.
