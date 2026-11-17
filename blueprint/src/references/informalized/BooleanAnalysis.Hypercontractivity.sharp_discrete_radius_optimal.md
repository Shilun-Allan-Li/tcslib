<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Discrete.lean :: BooleanAnalysis.Hypercontractivity.sharp_discrete_radius_optimal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimal radius for a two-point law

**Claim.** Under the stated two-point mass and parameter hypotheses, each of the two hypercontractivity assertions holds exactly when $\rho\leq\rho_*$, where $\rho_*=\sqrt{\sinh(u/q)/\sinh(u/(q/(q-1)))}$ and $u=\log((1-\lambda)/\lambda)$.

**Proof.** First, the two-point moment identity shows that $X$ has mean zero from the prescribed masses at $1-\lambda$ and $-\lambda$ (\texttt{FiniteLaw.centered_two_point_moments}). For the forward assertion, necessity follows by conjugating any forward hypercontractivity statement to the conjugate exponents and applying the two-point radius upper bound (\texttt{IsHypercontractive.conjugate}; \texttt{SharpDiscrete.two_point_conjugate_radius_le}). For sufficiency, the sharp forward theorem supplies the inequality at $\rho_*$, and radius monotonicity lowers it to the given $\rho\leq\rho_*$ (\texttt{SharpDiscrete.two_point_forward_sharp}; \texttt{IsHypercontractive.mono_radius}).

For the conjugate-exponent assertion, necessity is exactly the two-point radius upper bound applied directly (\texttt{SharpDiscrete.two_point_conjugate_radius_le}). Sufficiency follows from the sharp conjugate theorem at $\rho_*$ and the same radius monotonicity (\texttt{SharpDiscrete.two_point_conjugate_sharp}; \texttt{IsHypercontractive.mono_radius}). This proves both equivalences.

**Key facts.** `BooleanAnalysis.Hypercontractivity.FiniteLaw.centered_two_point_moments`, `BooleanAnalysis.Hypercontractivity.IsHypercontractive.conjugate`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_radius_le`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_forward_sharp`, `BooleanAnalysis.Hypercontractivity.IsHypercontractive.mono_radius`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_radius_le`, `BooleanAnalysis.Hypercontractivity.SharpDiscrete.two_point_conjugate_sharp`, `BooleanAnalysis.Hypercontractivity.IsHypercontractive.mono_radius`.
