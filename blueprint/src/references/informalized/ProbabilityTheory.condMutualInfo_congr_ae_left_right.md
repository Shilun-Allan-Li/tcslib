<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Conditioning.lean :: ProbabilityTheory.condMutualInfo_congr_ae_left_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-sure invariance in both arguments

**Claim.** If $X=X'$ and $Y=Y'$ almost everywhere, while the conditioning variable $Z$ is unchanged, then $I[X:Y\mid Z;\mu]=I[X':Y'\mid Z;\mu]$.

**Proof.** Express each conditional mutual information as the sum of the conditional entropies of its two arguments given $Z$, minus the conditional entropy of the pair given $Z$. By conditional entropy invariance under almost-everywhere equality (`condEntropy_congr_ae`), the terms for $X$ and $X'$ agree given $Z$, and so do the terms for $Y$ and $Y'$. The same invariance applies to the pair-valued variables $(X,Y)$ and $(X',Y')$, which agree almost everywhere because both component equalities hold almost everywhere; the conditioning variable is identical. Hence each term in the two expressions agrees, proving the result.

**Key facts.** `ProbabilityTheory.condEntropy_congr_ae`.
