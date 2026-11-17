<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.card_nat_in_Ico -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting integers in an interval

**Claim.** For $a\le b$, the number of indices $j\in\{0,\ldots,n-1\}$ with $a\le j<b$ is at most $b-a+1$.

**Proof.** Let $S$ be the set of indices satisfying $a\le j<b$. If $S$ is empty, the bound follows from $a\le b$. Otherwise let $j_{\rm lo}$ and $j_{\rm hi}$ be its least and greatest elements. Every element of $S$ lies among the integers from $j_{\rm lo}$ through $j_{\rm hi}$, so $|S|\le j_{\rm hi}-j_{\rm lo}+1$. Since $a\le j_{\rm lo}$ and $j_{\rm hi}<b$, this last quantity is at most $b-a+1$.
