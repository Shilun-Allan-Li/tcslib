<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.expect_centeredSingletonSquare_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Centered linear-square moment bound

**Claim.** If a sign-valued function has level-one Fourier weight $1-\delta$, with $0\leq\delta\leq1/1600$, then the expected square of its centered level-one linear form is at most $6400\delta$.

**Proof.** Write $a_i=\widehat f(\{i\})$, let $g$ be the centered linear square built from these coefficients, and put $V=\mathbb E g^2$. The identity for singleton coefficients gives $g(x)=(\deg_1 f(x))^2-(1-\delta)$ (`centeredLinearSquare_singletonCoeffs`).

If $\delta=0$, the expected squared error between $f$ and its degree-one projection is zero, by the error identity (`expect_toReal_sub_degreePart_one_sq`). Since each squared error is nonnegative, every such error vanishes, so the projection equals $f$ pointwise. The singleton-coefficient identity then gives $g=0$ everywhere, and the desired bound follows.

Now suppose $\delta>0$ and, seeking a contradiction, assume $V>6400\delta$. In particular $V>0$. The fourth-moment estimate for the centered linear square gives $\mathbb E g^4\leq81V^2$ (`centeredLinearSquare_fourthMoment_le`). The second-to-fourth moment probability bound therefore says that the event $V\leq4g(x)^2$ has probability at least $1/144$ (`one_div_144_le_uniformProbability_four_mul_sq_ge_secondMoment`). On this event, $g(x)$ is large enough that $1600\delta<((\deg_1 f(x))^2-(1-\delta))^2$. The elementary comparison lemma converts this to $1521\delta<((\deg_1 f(x))^2-1)^2$ (`sq_sub_one_far_of_centered_far`). Since $f(x)^2=1$ for a sign-valued function, the resulting pointwise estimate is $169\delta\leq(f(x)-\deg_1 f(x))^2$ (`exercise9_5`).

Averaging this pointwise lower bound on the event, and using nonnegativity off the event, shows that the expected squared projection error is at least $169\delta$ times the event probability, hence at least $169\delta/144$. But its exact value is $\delta$ (`expect_toReal_sub_degreePart_one_sq`), a contradiction since $\delta>0$ and $169/144>1$. Thus $V\leq6400\delta$.

**Key facts.** `FABL.expect_toReal_sub_degreePart_one_sq`, `FABL.centeredLinearSquare_singletonCoeffs`, `FABL.centeredLinearSquare_fourthMoment_le`, `FABL.one_div_144_le_uniformProbability_four_mul_sq_ge_secondMoment`, `FABL.sq_sub_one_far_of_centered_far`, `FABL.exercise9_5`.
