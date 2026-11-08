<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clPrev_native -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Native Computation of the Previous Visit

**Claim.** The optional-time code for the last time strictly before $T(x)$ when tape $\tau$ occupied its position at time $T(x)$ on input $0^{m(x)}$ is polynomial-time computable, assuming the unary inputs encoding $m(x)$ and $T(x)$ are polynomial-time computable.

**Proof.** Choose distinct positive and negative query coordinates corresponding to the two copies of tape $\tau$ in the search machine’s record. Their distinctness follows from their different offsets in the record. Apply the native-search result (`Complexity.clSearch_native`) to the input function $x\mapsto 0^{m(x)}$, the time bound $T(x)$, and these coordinates; the hypotheses give polynomial-time computability of the input and unary clock. This produces in polynomial time the code for the last successful match among times $s<T(x)$. At each such time, the scheduling identity (`Complexity.clMatchFlag_schedule`) says that the match flag is true exactly when tape $\tau$’s position at time $s$ equals its position at time $T(x)$. Thus the search’s successful times are exactly the previous visits in the definition. The last-match coding identity (`Complexity.clLastCode_prev`) identifies the resulting code with the required optional-time code, proving the claim.

**Key facts.** `Complexity.clSearch_native`, `Complexity.clMatchFlag_schedule`, `Complexity.clLastCode_prev`.
