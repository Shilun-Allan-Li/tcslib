<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integrableOn_upperTailFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of an Upper-Tail Function

**Claim.** If $\nu$ is a finite measure and $z\mapsto(z-t)^+$ is integrable with respect to $\nu$, then $u\mapsto\nu((t+u,\infty))$ is integrable on $(0,\infty)$.

**Proof.** The upper-tail function is measurable, hence strongly measurable on the restricted interval (measurability of the upper-tail function, `FABL.measurable_upperTailFrom`). For each $u>0$, the set where $u<(z-t)^+$ is exactly $(t+u,\infty)$ (`FABL.setOf_lt_posPart_sub_eq_Ioi_add`). The layer-cake formula therefore identifies the integral over $u>0$ of $\nu((t+u,\infty))$ with the integral of $(z-t)^+$ against $\nu$. That integral is finite by hypothesis. The tail values are nonnegative, so the function is integrable.

**Key facts.** `FABL.measurable_upperTailFrom`, `FABL.setOf_lt_posPart_sub_eq_Ioi_add`.
