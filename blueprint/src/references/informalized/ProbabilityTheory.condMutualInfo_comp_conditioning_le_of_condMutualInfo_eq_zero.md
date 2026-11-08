<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_comp_conditioning_le_of_condMutualInfo_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity Under Coarser Conditioning

**Claim.** If the conditional mutual information between $X$ and $W$ given $f(W)$ vanishes, then conditioning on $f(W)$ gives no more information between $X$ and $Y$ than conditioning on $W$.

**Proof.** Set $Z=f\circ W$. First, $(W,Z)$ determines $W$ and is itself determined by $W$, so the conditional entropy of $X$ given $(W,Z)$ equals that given $W$. This follows from invariance of conditional entropy under injective recoding (`condEntropy_of_injective'`). Next, expand the assumed identity $I[X:W\mid Z]=0$ as $H[X\mid Z]-H[X\mid(W,Z)]=0$. The preceding entropy equality then gives $H[X\mid Z]=H[X\mid W]$. Also, $(Y,Z)$ is a function of $(Y,W)$, so conditioning on $(Y,W)$ cannot leave more entropy in $X$ than conditioning on $(Y,Z)$; this is the conditional entropy monotonicity under a function (`condEntropy_comp_ge`). Expand both desired mutual informations as $H[X\mid Z]-H[X\mid(Y,Z)]$ and $H[X\mid W]-H[X\mid(Y,W)]$. Their first terms agree, and the entropy inequality for the second terms yields the result.
