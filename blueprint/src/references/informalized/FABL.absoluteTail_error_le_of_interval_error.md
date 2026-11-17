<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.absoluteTail_error_le_of_interval_error -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Absolute Tail Error from Interval Error

**Claim.** For probability measures $\nu$ and $\tau$ on $\mathbb R$, if the probabilities of $[-t,t]$ differ by at most $B$ for some $t\ge0$, then their absolute tail probabilities at $t$ differ by at most $B$.

**Proof.** For each probability measure, the absolute tail probability is one minus the probability of $[-t,t]$. Subtracting the two tail probabilities therefore gives the negative of the difference between the interval probabilities. Taking absolute values preserves the magnitude of that difference, so the assumed bound gives the conclusion.

**Key facts.** `FABL.absoluteTail_eq_one_sub_interval`.
