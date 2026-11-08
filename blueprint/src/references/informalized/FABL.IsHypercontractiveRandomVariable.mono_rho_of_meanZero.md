<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.IsHypercontractiveRandomVariable.mono_rho_of_meanZero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of the Contraction Parameter

**Claim.** Assume $\mathbb E[X]=0$, $p\ge1$, and $X$ is hypercontractive with parameters $p,q,\rho$, where $\rho>0$. Then it is hypercontractive with parameters $p,q,\rho'$ for every $0\le\rho'\le\rho$.

**Proof.** Set $\sigma=\rho'/\rho$. The sign assumptions give $0\le\sigma$, and $\rho'\le\rho$ gives $\sigma\le1$. The mean-zero self-hypercontractivity theorem says that $X$ is hypercontractive from exponent $p$ to itself with parameter $\sigma$ whenever $p\ge1$, the mean is zero, and $0\le\sigma\le1$ (`meanZero_qq_hypercontractive`). Compose this inequality with the assumed one from $p$ to $q$, using the composition rule (`IsHypercontractiveRandomVariable.comp`). The resulting parameter is $\rho\sigma$, which equals $\rho'$ by the definition of $\sigma$.

**Key facts.** `FABL.meanZero_qq_hypercontractive`, `FABL.IsHypercontractiveRandomVariable.comp`.
