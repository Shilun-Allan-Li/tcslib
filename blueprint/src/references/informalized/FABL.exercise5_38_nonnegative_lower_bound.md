<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/FKNImprovement.lean :: FABL.exercise5_38_nonnegative_lower_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegative lower bound from a squared estimate

**Claim.** Under the stated assumptions, the squared lower estimate implies $1-\delta/2-2\eta\le z$, where $\eta=16C^2\delta^2\max\{\log_2(1/(C\delta)),1\}$.

**Proof.** Let $L=1-\delta/2-2\eta$. If $L\le0$, then $L\le z$ follows from $z\ge0$. Otherwise $L>0$. The squared estimate (`FABL.exercise5_38b`) gives $L^2\le1-\delta-16C^2\delta^2\log_2(1/(C\delta))$. By the assumed lower bound on $z^2$, the right-hand side is at most $z^2$, so $L^2\le z^2$. Since both $L$ and $z$ are nonnegative, comparison of squares yields $L\le z$.

**Key facts.** `FABL.exercise5_38b`.
