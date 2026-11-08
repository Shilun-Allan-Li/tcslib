<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigCount.lean :: Turing.MultiTapeTM.ConfigCount.coreCode_inj -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of bounded core coding

**Claim.** If two configurations satisfy the stated bounds on their head positions and occupied tape cells, equality of their bounded core codes implies equality of their cores.

**Proof.** Equality of the codes gives equality of the states and input-head positions, equality of the encoded tape contents, and equality of the encoded work-head positions. Fix a tape and a cell position $z$. If $|z|\le B$, the integer $z$ corresponds to the bounded index $(z+B)$; evaluating the equality of encoded tape contents at that index shows that the two configurations have the same symbol at $z$. If $|z|>B$, neither configuration can have a symbol there: either nonblank value would contradict its occupied-cell bound. Thus the tape contents agree everywhere. Finally, the head positions agree tape by tape by injectivity of the bounded position code on positions whose absolute values are at most $B$ (`posCode_injOn`). Together with equality of state and input position, these are exactly the components of the core.

**Key facts.** `Turing.MultiTapeTM.ConfigCount.posCode_injOn`.
