<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Products/Applications.lean :: BooleanAnalysis.Hypercontractivity.product_stableInfluence_le_of_norm_noise_laplacian_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable influence from norm contraction

**Claim.** If the noise operator applied to the coordinate Laplacian contracts its norm from exponent \(2\) to exponent \(q/(q-1)\), then \(\rho\) times the stable influence is at most the ordinary influence raised to \(2-2/q\).

**Proof.** Put \(p=q/(q-1)\). Since \(q\ge2\), we have \(1\le p\le2\). The squared norm of the noisy coordinate Laplacian equals \(\rho\) times the stable influence (\(\texttt{product\_stableInfluence\_eq\_sq\_norm\_noise\_laplacian}\)). The assumed contraction therefore bounds this quantity by the square of the \(p\)-norm of the coordinate Laplacian. By the definition of the norm, that square is the \(p\)-moment of its absolute value raised to \(2/p\). For a Boolean function, the absolute-moment comparison for the Laplacian bounds its \(p\)-moment by the ordinary influence (\(\texttt{product\_laplacian\_abs\_moment\_le\_influence}\)). Raising this inequality to the nonnegative power \(2/p\) preserves it. Finally, substituting \(p=q/(q-1)\) gives \(2/p=2-2/q\), as required.

**Key facts.** `BooleanAnalysis.Hypercontractivity.product_stableInfluence_eq_sq_norm_noise_laplacian`, `BooleanAnalysis.Hypercontractivity.product_laplacian_abs_moment_le_influence`.
