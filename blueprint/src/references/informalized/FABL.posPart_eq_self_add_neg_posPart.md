<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/HammingBallLimit.lean :: FABL.posPart_eq_self_add_neg_posPart -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive Part Identity

**Claim.** For every real number $u$, its positive part satisfies $\max\{u,0\}=u+\max\{−u,0\}$.

**Proof.** If $u\geq0$, then $u^+=u$ and $(-u)^+=0$, so the identity holds. If $u<0$, then $u^+=0$ and $(-u)^+=-u$, so the right-hand side is also $u+(-u)=0$.
