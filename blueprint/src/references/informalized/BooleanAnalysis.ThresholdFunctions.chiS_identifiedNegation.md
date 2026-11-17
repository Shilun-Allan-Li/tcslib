<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/NoiseStability.lean :: BooleanAnalysis.ThresholdFunctions.chiS_identifiedNegation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Walsh Character Under Negated Identification

**Claim.** For the Boolean vector formed by pulling back $w$ along $\pi$ and complementing coordinates where $z$ is true, its Walsh character on $S$ equals $\chi_S(z)\chi_{O_\pi(S)}(w)$.

**Proof.** For each coordinate $i\in S$, its sign in the constructed vector is the sign of $w_{\pi(i)}$, multiplied by the sign of $z_i$: if $z_i$ is false the sign is unchanged, and if $z_i$ is true complementation reverses it. Multiplying these identities over $S$ separates the product into $\chi_S(z)$ and the product of the signs of $w_{\pi(i)}$. The latter product groups factors according to their target coordinate; each target sign appears as many times as its fiber in $S$, so even multiplicities cancel and odd multiplicities remain. Thus it is $\chi_{O_\pi(S)}(w)$ by the odd-fiber product identity (`prod_boolToSign_comp`).

**Key facts.** `BooleanAnalysis.ThresholdFunctions.prod_boolToSign_comp`.
