<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.one_div_144_le_uniformProbability_four_mul_sq_ge_secondMoment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform probability lower bound

**Claim.** Let $\Omega$ be finite and nonempty and $g:\Omega\to\mathbb R$. If the uniform average $m$ of $g^2$ is positive and the uniform average $q$ of $g^4$ is at most $81m^2$, then the uniform probability that $m\le4g(x)^2$ is at least $1/144$.

**Proof.** Let $m=\mathbb E g^2$, let $q=\mathbb E g^4$, and let $I(x)$ be the indicator of the event $m\le4g(x)^2$. Write $p=\mathbb E I$ for its uniform probability and $r=\mathbb E[g^2I]$. Pointwise, if the event holds then $g(x)^2\le m/4+g(x)^2I(x)$; if it fails, $g(x)^2<m/4$ and $I(x)=0$, so the same inequality holds. Averaging gives $m\le m/4+r$, hence $3m/4\le r$. Cauchy–Schwarz applied to $g^2$ and $I$ gives $r^2\le qp$, because $I^2=I$. The fourth-moment bound then implies $(3m/4)^2\le r^2\le qp\le81m^2p$. As $m>0$, division by $m^2$ yields $p\ge1/144$, as required.
