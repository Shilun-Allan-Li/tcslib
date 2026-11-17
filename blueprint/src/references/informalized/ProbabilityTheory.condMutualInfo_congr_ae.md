<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Conditioning.lean :: ProbabilityTheory.condMutualInfo_congr_ae -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Almost-sure invariance of conditional mutual information

**Claim.** If $X=X'$, $Y=Y'$, and $Z=Z'$ almost everywhere under the probability measure, then $I[X:Y\mid Z;\mu]=I[X':Y'\mid Z';\mu]$.

**Proof.** Write conditional mutual information as the sum of the conditional entropies of the two variables given $Z$, minus the conditional entropy of their pair given $Z$. The conditional entropy invariance theorem says that changing either argument almost everywhere does not change conditional entropy (`condEntropy_congr_ae`). Apply it first to $X$ and $Z$, then to $Y$ and $Z$. Apply it a third time to the pair-valued variables $(X,Y)$ and $(X',Y')$: their almost-everywhere equality follows by combining the assumed equalities for $X$ and $Y$, while the conditioning variables agree almost everywhere by hypothesis. Thus all three conditional entropy terms in the expression for mutual information agree, so the mutual informations are equal.

**Key facts.** `ProbabilityTheory.condEntropy_congr_ae`.
