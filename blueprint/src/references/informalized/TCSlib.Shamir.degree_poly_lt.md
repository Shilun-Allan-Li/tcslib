<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Cryptography/SecretSharing/Shamir.lean :: TCSlib.Shamir.degree_poly_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree bound for the sharing polynomial

**Claim.** When $k>0$ and $q$ has degree less than $k-1$, the polynomial $\mathrm{sec}+Xq$ has degree less than $k$.

**Proof.** First show that $Xq$ has degree less than $k$. If $q=0$, this product is zero and has degree below every natural-number bound. Otherwise, the degree bound on $q$ is its natural degree bound, so $\deg(q)<k-1$; multiplying by $X$ raises the degree by one, giving $\deg(Xq)<k$. The constant polynomial with value $\mathrm{sec}$ has degree at most zero, hence degree less than $k$ because $k>0$. The degree of a sum is at most the maximum of the summands' degrees, so $\mathrm{sec}+Xq$ also has degree less than $k$.
