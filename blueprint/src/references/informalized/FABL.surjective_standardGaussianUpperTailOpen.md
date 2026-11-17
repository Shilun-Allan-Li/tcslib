<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianIsoperimetric.lean :: FABL.surjective_standardGaussianUpperTailOpen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Range of the Gaussian Upper Tail

**Claim.** The standard Gaussian upper-tail function takes every value strictly between $0$ and $1$.

**Proof.** Fix a value $\alpha$ strictly between $0$ and $1$. The upper-tail function tends to $0$ as its argument tends to $+\infty$ (`FABL.tendsto_standardGaussianUpperTail_atTop`), so some argument has tail value below $\alpha$. It tends to $1$ as its argument tends to $-\infty$ (`FABL.tendsto_standardGaussianUpperTail_atBot`), so some argument has value above $\alpha$. The function is continuous (`FABL.continuous_standardGaussianUpperTail`); hence the intermediate value theorem gives an argument where its value is exactly $\alpha$. This proves surjectivity onto the open interval.

**Key facts.** `FABL.tendsto_standardGaussianUpperTail_atTop`, `FABL.tendsto_standardGaussianUpperTail_atBot`, `FABL.continuous_standardGaussianUpperTail`.
