<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.matrixBilinearNonzeroProbability_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bilinear Nonzero Probability Identity

**Claim.** For an $n\times n$ matrix $D$ over $\mathbb F_2$, and independent uniformly distributed vectors $x,y\in\mathbb F_2^n$, the probability that $x\cdot(Dy)$ is nonzero equals one half the probability that $Dy$ is nonzero for uniform $y$.

**Proof.** Express the joint uniform average as an iterated average, first over $x$ and then over $y$, and exchange the order of these finite averages. By symmetry of the dot product, for each fixed $y$ the inner event is that $(Dy)\cdot x$ is nonzero. The nonzero-dot-product probability fact (\texttt{uniformProbability_f₂DotProduct_ne_zero}) says this inner probability is zero when $Dy=0$, and otherwise is $1/2$. Thus the integrand as a function of $y$ is exactly $(1/2)$ times the indicator that $Dy\ne0$. Taking the average over $y$ factors out the constant $1/2$, giving the claimed identity.

**Key facts.** `FABL.uniformProbability_f₂DotProduct_ne_zero`.
