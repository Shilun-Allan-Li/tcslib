<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCmp_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact Comparator Runtime

**Claim.** For every Boolean input word, valid input-head position, and four Boolean words, running the comparator for twice the maximum word length plus two steps reaches its completed control with the final verdict computed after processing that many columns. The work words and input-head position are unchanged, all work heads are at zero, and the output is empty.

**Proof.** Let $m$ be the maximum of the four word lengths. The forward-pass result (`clCmp_forward`) says that after $m$ steps the comparator is in its reading control, its accumulator is the state obtained after processing $m$ columns, and its work heads are at position $m$. One further step applies the scan-completion transition (`clCmp_finish_scan`): it computes the final verdict and enters the intermediate control with the heads at $m-1$. The rewind result (`clCmp_rewind`), applied with this verdict and $j=m$, shows that the next $m+1$ steps reach the completed control and return the heads to zero, preserving the words and the other configuration data. Splitting the total run into these consecutive segments gives $m+1+(m+1)=2m+2$ steps, as claimed.

**Key facts.** `Complexity.clCmp_forward`, `Complexity.clCmp_finish_scan`, `Turing.MultiTapeTM.runFrom_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.clCmp_rewind`.
