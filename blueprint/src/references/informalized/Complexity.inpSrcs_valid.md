<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigCircuit.lean :: Complexity.inpSrcs_valid -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Validity of Input-Cell Sources

**Claim.** Under the stated validity assumption on the source list, every source in the input-cell source list at time $t$ and position $p$ is valid for input length $n$, width $W=\operatorname{snapWidth}(M)+5$, and the specified input-cell index.

**Proof.** Let $i$ be the specified index. First, the definition of the input index gives $t\,\operatorname{cfgStride}\le i$. Also, each bit position below $5$ is below the width $W$, since $W=\operatorname{snapWidth}(M)+5$. We check the sources by their forms. Constants are always valid. The source chosen from $\ell$ is either a constant or a member of $\ell$: when it is a member, the hypothesis gives validity at block index $0$, and therefore its block index is below the larger index $i$ as well. For each previous-step input source, if its Boolean guard is true, then $t\ne0$ and its position $p'$ is below $|\ell|+2$. The input-index-before-next-block bound (`inpIdx_lt_succ`) puts its block index below $(t-1+1)\,\operatorname{cfgStride}$, and the previous-step comparison (`prevStep_lt`) then puts that block index below $i$; its bit position is $0<W$. If the guard is false, the source is a constant. The two same-time input-chain sources are likewise constants when $p=0$; otherwise their block index is below $i$ by the index formula, and their bit positions $1,2$ are below $W$. Finally, each previous-snapshot source is valid at index $i$ by the previous-snapshot validity result (`prevSnapSrcs_valid`), using $t\,\operatorname{cfgStride}\le i$. These cases cover every member of the input-cell source list.

**Key facts.** `Complexity.inpIdx_lt_succ`, `Complexity.prevStep_lt`, `Complexity.prevSnapSrcs_valid`.
