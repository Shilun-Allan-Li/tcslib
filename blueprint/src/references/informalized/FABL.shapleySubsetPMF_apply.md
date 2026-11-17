<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleySubsetPMF_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Subset of Fixed Size

**Claim.** Choosing a size uniformly from $0,1,\ldots,n$ and then choosing uniformly among subsets of that size assigns $S$ probability $1/((n+1)\binom{n}{|S|})$.

**Proof.** Expand the probability of $S$ under the two-stage choice as a sum over all possible sizes. Only the size $|S|$ contributes, because $S$ belongs to the layer of subsets of size $k$ exactly when $k=|S|$. At that size, the first choice has probability $1/(n+1)$, and the uniform choice within the layer has probability $1/\binom{n}{|S|}$, since that layer contains $\binom{n}{|S|}$ subsets. Multiplying these probabilities gives the formula.
