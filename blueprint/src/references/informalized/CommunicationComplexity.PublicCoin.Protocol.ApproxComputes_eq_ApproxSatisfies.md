<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PublicCoinBasic.lean :: CommunicationComplexity.PublicCoin.Protocol.ApproxComputes_eq_ApproxSatisfies -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Approximate Computation as Satisfaction

**Claim.** A public-coin protocol approximately computes $f$ at tolerance $\varepsilon$ exactly when it approximately satisfies the predicate asserting that its output equals $f(x,y)$.

**Proof.** Expand both propositions. At each input pair, the first bounds the measure of the coin outcomes for which the protocol's output differs from $f(x,y)$. The second bounds the measure of outcomes for which the predicate fails; for the predicate $a=f(x,y)$, failure means precisely that the output $a$ is unequal to $f(x,y)$. Thus the measured sets, and hence the inequalities for every input pair, are identical.
