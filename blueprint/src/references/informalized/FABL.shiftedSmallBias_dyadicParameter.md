<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.shiftedSmallBias_dyadicParameter -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dyadic Parameter Identity

**Claim.** If $t\le\ell$ and $n=2^{\ell-t}$, then $(n-1)/2^\ell=(1/2)^t-(1/2)^\ell$.

**Proof.** Substitute $n=2^{\ell-t}$. The assumption $t\le\ell$ ensures $2^{\ell-t}\ge1$, so $n-1$ can be cast to the reals as $2^{\ell-t}-1$. Split the quotient as $2^{\ell-t}/2^\ell-1/2^\ell$. The dyadic field ratio identity (\texttt{dyadicFieldRatio\_eq\_invPow}) identifies the first term with $(1/2)^t$, while $1/2^\ell=(1/2)^\ell$. Subtracting gives the result.

**Key facts.** `FABL.dyadicFieldRatio_eq_invPow`.
