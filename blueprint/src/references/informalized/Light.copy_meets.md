<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Copy.lean :: Light.copy_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded-time memory copy

**Claim.** Under the stated bounds and disjointness hypotheses, the copy routine has an execution at depth $d$ of cost at most $16n+6$ that copies each source cell to its corresponding destination cell and preserves memory outside the destination interval.

**Proof.** Apply the execution theorem for a pass loop (Ends.pass) with the loop index ranging over $0,\ldots,n-1$ and the value copied in round $i$ equal to $\mu(\mathrm{src}+i)$. The hypotheses provide the address and word bounds needed for the pass; its invariant says that after $j$ rounds, destination cells already written contain their corresponding source values, while memory outside the destination interval remains unchanged. For round $i$, the read address $\mathrm{src}+i$ lies outside the destination interval by disjointness, so earlier writes have not changed it; thus the round reads the original value $\mu(\mathrm{src}+i)$. After all rounds, the invariant gives every required copied value and the unchanged-memory property. The pass theorem supplies the cost bound $16n+6$. Finally, the fact that the program entry is the copy body turns this execution into the claimed routine execution (Meets.of_body).

**Key facts.** `Light.Ends.pass`, `Light.wrote_done`, `Light.wrote_rest`, `Light.Meets.of_body`.
