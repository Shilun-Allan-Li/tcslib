<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/JuntaStableInfluence.lean :: FABL.exists_stableInfluence_ge_of_isKJunta_of_nonconstant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Stable Influence of a Junta

**Claim.** For a nonconstant Boolean function depending on at most $k$ coordinates and $\delta\in[0,1]$, some coordinate has stable influence at least $(\tfrac12-\tfrac\delta2)^{k-1}/k$.

**Proof.** Choose a set $J$ of at most $k$ coordinates on which the function depends. This set cannot be empty: dependence on no coordinates would make the function constant. Thus $k>0$. The junta degree bound says the Fourier degree is at most $k$. The variance lower bound for a nonconstant Boolean function of degree at most $k$ gives $2^{-(k-1)}\le\operatorname{Var}(f)$. Put $\rho=1-\delta$, which lies in $[0,1]$. The spectral lower bound for total stable influence then gives $\rho^{k-1}\operatorname{Var}(f)\le I^{\mathrm{tot}}_\rho(f)$. Combining the bounds and using $\rho/2=\tfrac12-\tfrac\delta2$ shows that $(\tfrac12-\tfrac\delta2)^{k-1}\le I^{\mathrm{tot}}_\rho(f)$. Because the function depends only on $J$, total stable influence is the sum of its coordinate stable influences over $J$. If every coordinate in $J$ had stable influence less than $(\tfrac12-\tfrac\delta2)^{k-1}/k$, their sum would be less than this threshold times $|J|\le k$, contradicting the preceding lower bound. Hence one coordinate in $J$ attains at least the stated bound.

**Key facts.** `FABL.fourierDegree_toReal_le_of_isKJunta`, `FABL.inv_two_pow_pred_le_variance_of_fourierDegree_le`, `FABL.pow_pred_mul_variance_le_totalStableInfluence_of_fourierDegree_le`, `FABL.totalStableInfluence_eq_sum_of_dependsOn`.

**Caveat.** The informal payload also mentions an unbiased-junta formulation and a separate example involving majority. Those are not conclusions of the formal theorem supplied here, so this account addresses only the theorem's stated stable-influence bound.
