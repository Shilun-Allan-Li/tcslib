<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.sq_sub_one_far_of_centered_far -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered Deviation Forces a Larger Deviation

**Claim.** If $\delta\le1/1600$ and $1600\delta<(t^2-(1-\delta))^2$, then $1521\delta<(t^2-1)^2$.

**Proof.** Suppose instead that $(t^2-1)^2\le1521\delta$. The bound on $\delta$ implies $\delta\le1$ and $\delta^2\le\delta$. Nonnegativity of $((t^2-1)-39\delta)^2$ gives a lower bound on $(t^2-1)^2-78\delta(t^2-1)+1521\delta^2$. Combining this with the supposition and $\delta^2\le\delta$ yields $(t^2-(1-\delta))^2\le1600\delta$, contradicting the strict hypothesis. Therefore the asserted strict inequality holds.
