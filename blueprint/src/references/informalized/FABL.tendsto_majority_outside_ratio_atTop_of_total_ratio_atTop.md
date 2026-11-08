<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.tendsto_majority_outside_ratio_atTop_of_total_ratio_atTop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outside-coordinate ratio divergence

**Claim.** If $m(q)\to\infty$ and $k(q)/\sqrt{k(q)+m(q)}\to\infty$, then $k(q)/\sqrt{m(q)}\to\infty$.

**Proof.** Eventually $m(q)>0$, and $m(q)\le k(q)+m(q)$. Monotonicity of the square root gives $\sqrt{m(q)}\le\sqrt{k(q)+m(q)}$. Dividing the nonnegative numerator $k(q)$ by these positive denominators yields $k(q)/\sqrt{k(q)+m(q)}\le k(q)/\sqrt{m(q)}$ eventually. Thus the latter ratio also tends to infinity by comparison.
