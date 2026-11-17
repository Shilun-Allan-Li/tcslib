<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.uniformApprox_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform Approximation Error Bound

**Claim.** For each target index $i$, the fraction of grid points sent to $i$ by the inverse-CDF approximation is at most its probability plus $1/n$.

**Proof.** First, monotonicity of the CDF gives $\mathrm{cdf}(p,i)\le\mathrm{cdf}(p,i+1)\le1$, where the second inequality follows by monotonicity up to the endpoint and the total-mass identity (\texttt{cdf\_mono}; \texttt{cdf\_one}). Thus both CDF values are finite. If a grid point $j/n$ is sent to $i$, the inverse-CDF characterization (\texttt{invCdf\_eq\_iff}) places it in the half-open interval $[\mathrm{cdf}(p,i),\mathrm{cdf}(p,i+1))$. Converting the inequalities from extended nonnegative reals to reals and multiplying by the positive number $n$ shows that the integer $j$ lies in the real interval $[n\,\mathrm{cdf}(p,i),n\,\mathrm{cdf}(p,i+1))$.

The number of integers among the $n$ grid indices in any half-open interval $[a,b)$ is at most $b-a+1$ (\texttt{card\_nat\_in\_Ico}). Therefore the number of grid points mapped to $i$ is at most $n(\mathrm{cdf}(p,i+1)-\mathrm{cdf}(p,i))+1$. By the successor recurrence, the difference of these CDF values is $p(i)$ (\texttt{cdf\_succ}); taking real values and dividing the count bound by $n>0$ yields the claimed upper bound.

**Key facts.** `CommunicationComplexity.Internal.cdf_mono`, `CommunicationComplexity.Internal.cdf_one`, `CommunicationComplexity.Internal.invCdf_eq_iff`, `CommunicationComplexity.Internal.card_nat_in_Ico`, `CommunicationComplexity.Internal.cdf_succ`.
