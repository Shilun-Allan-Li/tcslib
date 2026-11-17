<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/ChainRules.lean :: ProbabilityTheory.condMutualInfo_le_prod_right_snd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adjoining a variable increases conditional information

**Claim.** The conditional mutual information between $X$ and $W$ given $Z$ is at most that between $X$ and the pair $(Y,W)$ given $Z$.

**Proof.** The pair $(Y,W)$ contains the coordinate $W$, recovered by projecting onto the second coordinate. The conditional data processing inequality says that applying measurable functions to the two variables in a conditional mutual information cannot increase it; apply this with the identity on $X$ and the second-coordinate projection on $(Y,W)$. The resulting inequality is $I[X:W\mid Z;\mu]\le I[X:(Y,W)\mid Z;\mu]$.

**Caveat.** The proof invokes the conditional data processing inequality (\texttt{condMutual\_comp\_comp\_le}), but that fact is not listed in the supplied upstream entries.
