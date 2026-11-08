<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/UPathLoops.lean :: Complexity.LogProg.ups_cp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy-Step Preservation of Probabilistic Semantics

**Claim.** If the registers are bounded by $B$, the destination value is at most the source value, and the entry state after replacing the destination by the source value has probabilistic semantics $p$, then the copy instruction at the given site with the original register state has probabilistic semantics $p$.

**Proof.** At the copy site, the program compares the destination and source registers. If they are equal, it proceeds directly to the designated entry state. Otherwise it increments the destination and returns to the comparison. Since the destination starts no larger than the source, this loop terminates with the destination equal to the source, while all register values remain bounded by $B$. The distinctness hypothesis ensures the increment does not change the source. The resulting configuration is exactly the one in the premise, so the copy-loop preservation theorem for probabilistic semantics (`psem_copy`) yields the same semantics $p$. The initial register bound supplies the bound required by that theorem (`UReg.reg`).

**Key facts.** `Complexity.LogProg.UReg.reg`, `Complexity.LogProg.psem_copy`.
