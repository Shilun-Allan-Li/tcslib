<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majority_outside_ratio_of_total_ratio -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outside-coordinate ratio limit

**Claim.** If $m(q)\to\infty$ and $k(q)/\sqrt{k(q)+m(q)}\to t$, then $k(q)/\sqrt{m(q)}\to t$.

**Proof.** Set $n(q)=k(q)+m(q)$, which tends to infinity because $m(q)$ does. Hence $1/\sqrt{n(q)}\to0$. Multiplying this by the assumed convergent ratio shows $k(q)/n(q)\to0$. Since $m(q)/n(q)=1-k(q)/n(q)$, it follows that $m(q)/n(q)\to1$. Taking square roots gives $\sqrt{m(q)}/\sqrt{n(q)}\to1$. Dividing the assumed ratio by this last ratio, whose limit is nonzero, gives $k(q)/\sqrt{m(q)}\to t$.
