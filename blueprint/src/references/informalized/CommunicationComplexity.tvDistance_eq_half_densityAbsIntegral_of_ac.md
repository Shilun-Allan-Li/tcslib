<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.tvDistance_eq_half_densityAbsIntegral_of_ac -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total Variation and Density Deviation

**Claim.** If probability measure $\mu$ is absolutely continuous with respect to probability measure $\nu$, then their total variation distance is one half the $L^1(\nu)$ deviation of the density from $1$.

**Proof.** By the characterization of total variation distance as the integral of the positive part of the density difference ($\texttt{tvDistance\_eq\_densityPositiveIntegral\_of\_ac}$), the distance equals the density's positive-part integral. The identity relating that positive-part integral to half the absolute-deviation integral ($\texttt{densityPositiveIntegral\_eq\_half\_densityAbsIntegral\_of\_ac}$) then gives the result.

**Key facts.** `CommunicationComplexity.tvDistance_eq_densityPositiveIntegral_of_ac`, `CommunicationComplexity.densityPositiveIntegral_eq_half_densityAbsIntegral_of_ac`.
