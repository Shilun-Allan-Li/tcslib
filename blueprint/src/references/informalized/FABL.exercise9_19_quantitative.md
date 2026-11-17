<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LevelWeightAsymptotics.lean :: FABL.exercise9_19_quantitative -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quantitative low-degree Fourier bound

**Claim.** For a Boolean-valued function of mean $\alpha$, if $k\le (373/1000)\log(1/\alpha)$, then its Fourier weight on sets of size at most $k$ is at most $\alpha^{21/20}$.

**Proof.** Apply the low-degree noise bound with noise parameter $\rho=1/4$. Since $2/(1+\rho)=8/5$, it gives $W_{\le k}(f)\le 4^k\alpha^{8/5}$. The hypothesis on $k$, multiplied by the nonnegative number $\log 4$, implies $4^k\le \alpha^{-(373/1000)\log 4}$: take logarithms, use $\log(1/\alpha)=-\log\alpha$, and exponentiate. Multiplying these bounds and combining powers of the positive base $\alpha$ gives $W_{\le k}(f)\le \alpha^{8/5-(373/1000)\log 4}$. The exponent estimate $(21/20)\le 8/5-(373/1000)\log 4$ (the bound `exercise9_19_exponent_bound`) and $0<\alpha\le1$ then imply the claimed upper bound, since powers of a base in $(0,1]$ decrease as the exponent increases.

**Key facts.** `FABL.fourierWeightAtMost_le_invPow_mul_rpow`, `FABL.exercise9_19_exponent_bound`.
