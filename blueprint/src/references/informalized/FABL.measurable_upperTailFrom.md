<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.measurable_upperTailFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Measurability of an Upper Tail Function

**Claim.** For every finite measure $\nu$ on $\mathbb{R}$ and every $t\in\mathbb{R}$, the function $u\mapsto\nu((t+u,\infty))$ is measurable.

**Proof.** If $u\le v$, then $t+u\le t+v$, so $(t+v,\infty)\subseteq(t+u,\infty)$. Thus the upper-tail function is antitone. Every real-valued antitone function on $\mathbb{R}$ is measurable, and finiteness of $\nu$ ensures the values are real.
