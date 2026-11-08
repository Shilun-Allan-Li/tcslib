<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Embed.lean :: Turing.embedSlot_selected -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Embedded Tape Index Is Selected

**Claim.** At the tape index $\iota(i)$, the selected slot is exactly $i$.

**Proof.** The selected slot is the first index $j$ in the finite list of all slots for which $\iota(j)=\iota(i)$. If no such index were found, then $i$ itself would satisfy the search predicate, a contradiction. Hence some $j$ is found, and the defining predicate gives $\iota(j)=\iota(i)$. Injectivity of $\iota$ forces $j=i$, so the selected slot is precisely $i$.
