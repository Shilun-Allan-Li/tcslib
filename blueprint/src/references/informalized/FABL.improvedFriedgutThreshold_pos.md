<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/ImprovedFriedgut.lean :: FABL.improvedFriedgutThreshold_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positivity of the Threshold

**Claim.** Under the stated hypotheses, the threshold $\Theta(f,\epsilon,\eta,k)$ is positive.

**Proof.** By definition, the threshold is the real power $1+\eta$ of $(\epsilon/T(f))\rho(\eta)^k$. The quotient is positive because $\epsilon>0$ and $T(f)>0$. Also $\rho(\eta)>0$ (`improvedFriedgutRho_pos`), so its natural power is positive. Their product is therefore positive, and a real power of a positive base is positive.

**Key facts.** `FABL.improvedFriedgutRho_pos`.
