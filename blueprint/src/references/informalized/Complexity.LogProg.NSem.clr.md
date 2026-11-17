<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.clr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of Clearing a Register

**Claim.** If the instruction at $l$ clears register $r$ and proceeds to $l'$, the current configuration satisfies $G$, and the successor with register $r$ set to zero satisfies the termination and acceptance semantics for $P$, then the current configuration satisfies those semantics as well.

**Proof.** The instruction is deterministic, so apply the deterministic-step semantics lemma using the guard at the current configuration (`NSem.det`). The step semantics for clearing a register sends $(l,v,res)$ to $(l',\operatorname{update}(v,r,0),res)$, exactly the successor assumed to satisfy the semantics. This identifies the required successor and completes the transfer.

**Key facts.** `Complexity.LogProg.NSem.det`.
