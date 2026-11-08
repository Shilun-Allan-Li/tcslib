<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.absoluteTail_eq_one_sub_interval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Tail Complement Identity

**Claim.** For a probability measure $\nu$ on $\mathbb R$ and $t\ge 0$, the measure of $\{x:t<|x|\}$ is one minus the measure of $[-t,t]$.

**Proof.** The condition $t<|x|$ is exactly the negation of $|x|\le t$. Since $t\ge0$, the inequality $|x|\le t$ is equivalent to $-t\le x\le t$, so the tail set is the complement of $[-t,t]$. The probability of a measurable complement is one minus the probability of the set, giving the identity.
