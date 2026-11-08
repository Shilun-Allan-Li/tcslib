<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTab.lean :: Complexity.Meyer.Tab_mem_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential Time for Tabulation

**Claim.** For every finite-state Turing machine over the Boolean alphabet, the language accepted by its tabulation procedure belongs to exponential time.

**Proof.** By the running-time bound for the tabulating machine (`tabTM_computes`), on an input word $y$ it computes the tabulation function in at most $10(|y|+1)2^{|y|}$ steps. The indicator of the language agrees with this Boolean output, so it remains to place this time bound below an exponential-time bound. Since $|y|+1\le 2^{|y|}$ and $2|y|\le |y|^2+1$, we have
\[
10(|y|+1)2^{|y|}\le 10\cdot 2^{2|y|}\le 10\cdot 2^{|y|^2+1}=20\cdot 2^{|y|^2}.
\]
Thus the machine decides the tabulation language within $20\cdot 2^{n^2}$ steps on inputs of length $n$, which is one of the allowed exponential time bounds.

**Key facts.** `Complexity.Meyer.tabTM_computes`.
