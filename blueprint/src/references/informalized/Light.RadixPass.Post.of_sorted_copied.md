<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/RadixPass.lean :: Light.RadixPass.Post.of_sorted_copied -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Radix pass after copying sorted indices

**Claim.** Under the radix-pass precondition, the count-sort postcondition, and the stated copying and memory-agreement assumptions, the resulting memory satisfies the radix-pass postcondition.

**Proof.** Write $k(j)=kd(\pi_j)$, with out-of-range entries interpreted as $0$. The count-sort result supplies the placement and counter-start equations, together with agreement between the initial and sorted memories outside the destination and counter regions. The assumed agreement between the sorted and final memories outside the copied segment therefore gives the required radix-pass memory agreement; at counter cells it also transfers the count-sort starting values, which are exactly the required counts for $k$. For the sorted segment, apply the stable-pass existence theorem (`Light.exists_stablePass`) to the count-sort placement equation: at each position determined by the stable sort rank, the sorted destination cell contains the corresponding entry of $\pi$. This produces a list $\pi'$ that is a stable pass of $\pi$ and whose entries are represented by the sorted destination segment. Finally, the copying hypothesis identifies each cell of the final segment with the corresponding sorted destination cell. Since $\pi'$ has the same length as $\pi$, these copied values show that the final segment represents $\pi'$, completing the postcondition.

**Key facts.** `Light.exists_stablePass`.
