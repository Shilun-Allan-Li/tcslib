<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.setOf_lt_posPart_sub_eq_Ioi_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive-Part Threshold Set

**Claim.** If $u>0$, the set of real $z$ for which $u<\max(z-t,0)$ is the open ray $(t+u,\infty)$.

**Proof.** For each $z$, the inequality $u<\max(z-t,0)$ holds exactly when one of $u<z-t$ or $u<0$ holds. Because $u>0$, the second alternative is impossible, so the condition is equivalent to $u<z-t$, or $t+u<z$. This is precisely membership in the open ray $(t+u,\infty)$.
