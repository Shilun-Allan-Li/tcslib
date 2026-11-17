<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveApplications.lean :: FABL.smallSetExpansion_conditional -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conditional small-set expansion bound

**Claim.** If $f$ takes only the values $0$ and $1$, has mean $\alpha>0$, and $0\leq\rho\leq1$, then the probability that both entries of a $\rho$-correlated pair lie in the event $f=1$, divided by $\alpha$, is at most $\alpha^{(1-\rho)/(1+\rho)}$.

**Proof.** Since $\alpha>0$, it suffices to prove the equivalent inequality obtained by multiplying by $\alpha$. The small-set expansion event bound (\texttt{FABL.smallSetExpansion_event}) bounds the joint event probability by $\alpha^{2/(1+\rho)}$. The exponents satisfy $2/(1+\rho)=1+(1-\rho)/(1+\rho)$. Because $\alpha>0$, the real-power addition law rewrites this upper bound as $\alpha\,\alpha^{(1-\rho)/(1+\rho)}$. Dividing by $\alpha$ yields the claim.

**Key facts.** `FABL.smallSetExpansion_event`.
