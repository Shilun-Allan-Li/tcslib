<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgutThreshold_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold power identity

**Claim.** Under the stated positivity assumptions, raising the improved Friedgut threshold to the power $1/(1+\eta)$ recovers its base, $\frac{\epsilon}{I(f)}\left(\frac{\eta}{2+\eta}\right)^k$.

**Proof.** Write $b=\frac{\epsilon}{I(f)}\rho^k$, where $\rho=\eta/(2+\eta)$. Since $\epsilon>0$, $I(f)>0$, and $\rho>0$ (by positivity of the improved Friedgut ratio, `improvedFriedgutRho_pos`), we have $b>0$. The threshold is $b^{1+\eta}$. The law $(x^p)^q=x^{pq}$ for nonnegative bases therefore gives $(b^{1+\eta})^{1/(1+\eta)}=b^{(1+\eta)/(1+\eta)}$. As $1+\eta>0$, the exponent simplifies to $1$, and $b^1=b$.

**Key facts.** `FABL.improvedFriedgutRho_pos`.
