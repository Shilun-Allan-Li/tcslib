<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Expanders/Walks.lean :: Expander.walkPMF_succ_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of an Extended Walk

**Claim.** The probability of a walk obtained by appending state $j$ to a walk $g$ is the probability of $g$ multiplied by the transition probability from its final state to $j$.

**Proof.** The extended-walk distribution is defined by first drawing a length-$k$ walk and then drawing a next state from the transition distribution at its endpoint. In the resulting mixture, only the prefix $g$ can produce the particular extended walk formed by appending $j$: any other prefix would remain different after taking the initial segment of the extended walk. For that prefix, only the choice of next state $j$ produces the specified extension. The probability is therefore the probability of $g$ times the transition probability from $g$'s final state to $j$, namely $\operatorname{ENNReal.ofReal}(A_{g_kj})$.
