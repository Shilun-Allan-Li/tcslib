<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Space.lean :: Randomized.compl_mem_BPL -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPL Is Closed Under Complement

**Claim.** For every language $L$ over the Boolean alphabet, if $L$ belongs to BPL, then its complement also belongs to BPL.

**Proof.** BPL is the bounded-space randomized class at the logarithmic space bound. Apply the general complement-closure theorem for BPSPACE, which preserves the space bound $s$ while replacing $L$ by its complement (compl_mem_BPSPACE). Taking $s$ to be logarithmic space gives $L^c\in\mathrm{BPL}$.

**Key facts.** `Randomized.compl_mem_BPSPACE`.
