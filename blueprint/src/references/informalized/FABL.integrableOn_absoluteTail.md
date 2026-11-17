<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integrableOn_absoluteTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of the Absolute Tail

**Claim.** If $\nu$ is a finite measure on $\mathbb{R}$ and $x\mapsto |x|$ is integrable with respect to $\nu$, then the absolute tail is integrable on $(0,\infty)$.

**Proof.** The tail function is measurable, so it is strongly measurable after restricting to $(0,\infty)$ (measurability of the absolute tail, `FABL.measurable_absoluteTail`). To prove integrability it remains to bound its integral. The layer-cake formula identifies the integral over $t>0$ of $\nu(\{x:t<|x|\})$ with the integral of $|x|$ with respect to $\nu$. Since the latter is finite by hypothesis, the tail has finite integral. The tail values are nonnegative, so this establishes integrability.

**Key facts.** `FABL.measurable_absoluteTail`.
