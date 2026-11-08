<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timed_pair_get -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubled Code Bits

**Claim.** For Boolean words $\alpha,x$ and $j<|\alpha|$, the pair encoding has the bit $\alpha_j$ at both positions $2j$ and $2j+1$.

**Proof.** Induct on $\alpha$, allowing the index $j$ to vary. The empty word has no index satisfying the hypothesis. For $\alpha=b::\alpha_0$, if $j=0$, the first two entries of the encoding are both $b$, as required. If $j=j_0+1$, the first two entries are again the doubled bit $b$; after these entries are removed, the remaining encoding has the same form with code word $\alpha_0$. The induction hypothesis applies at $j_0$, and the index arithmetic identifies the original positions $2j$ and $2j+1$ with the corresponding positions in that tail.
