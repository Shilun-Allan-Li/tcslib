<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UniformTableauSpec.lean :: Complexity.UTab.cellS_toBitSrc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cell Source Translation

**Claim.** Under the stated register-index hypotheses, translating the cell source list for time $t$ and position $r$ gives exactly the prescribed bit-source list for cell $(t,\tau,r)$.

**Proof.** First separate the snapshot portion of the source list from its cell-specific prefix. The snapshot portion translates to the preceding-snapshot sources by the snapshot translation identity (`Complexity.UTab.psnS_toBitSrc`). The length hypothesis on the input list identifies its length with $N$, so the remaining comparison is between the translated cell prefix and the prefix defining the target list.

Now split on whether $t=0$. If $t=0$, the boundary flags and the source definitions make all previous-time neighbor sources constant false; the current-cell sources are likewise handled according to whether $r=0$. The current instruction index hypothesis identifies the current block, and the two cases for $r$ establish the required source equalities.

If $t\ne0$, the hypothesis relating the preceding-cell register to the current instruction index, together with the stride layout, identifies the preceding block index with that of cell $(t-1,\tau,r)$. The proof then splits according to whether $r<2T$, which determines whether the right-neighbor flag enables that source, and further according to whether $r=0$, which determines whether the left-neighbor source is enabled. In each case, the definitions of the neighbor and current-source constructors give the prescribed block or false-constant entries. The stride arithmetic aligns the block indices. Combining these prefix equalities with the snapshot equality proves the list identity.

**Key facts.** `Complexity.UTab.psnS_toBitSrc`.
