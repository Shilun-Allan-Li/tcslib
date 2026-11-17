<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integrableOn_nonuniformTailBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Cubic Tail Bound

**Claim.** For every $K\in\mathbb{R}$, the function $t\mapsto 2K/(1+t^3)$ is integrable on $(0,\infty)$.

**Proof.** The function is the constant multiple $2K$ of $t\mapsto(1+t^3)^{-1}$. Multiplying an integrable function by a finite real constant preserves integrability, so the preceding reciprocal-cubic integrability result gives the claim.

**Key facts.** `FABL.integrableOn_inv_one_add_cube`.
