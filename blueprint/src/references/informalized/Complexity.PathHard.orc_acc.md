<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardRegs.lean :: Complexity.PathHard.orc_acc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance oracle on encoded queries

**Claim.** The oracle at index $3$, on the specified encoding of $(x,\beta)$ and $(u,s)$, returns true exactly when the corresponding encoding of $(x,u,s)$ belongs to $N$'s acceptance language.

**Proof.** The oracle is the indicator of the language selected by its index, and an indicator equals the decidable truth value of membership (`indicator_eq_decide`). At index $3$ the selected language tests whether `dropIdx` of the query belongs to the acceptance language. Applying `dropIdx_pairEncode` to the nested pair encoding reduces that membership test to membership of the encoding of $(x,u,s)$ itself. Thus the oracle answer is exactly the stated truth value.

**Key facts.** `Complexity.LogProg.indicator_eq_decide`, `Complexity.dropIdx_pairEncode`.
