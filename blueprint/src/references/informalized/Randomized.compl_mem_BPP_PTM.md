<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Randomized.compl_mem_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BPP Is Closed Under Complement

**Claim.** For every language $L$ over the Boolean alphabet, if $L$ belongs to BPP, then its complement belongs to BPP.

**Proof.** Membership in BPP means membership in BPTIME for some polynomial bound indexed by an exponent $c$. Fix such a $c$. The bounded-time complement theorem gives $L^c$ in BPTIME with that same time bound (compl_mem_BPTIME). Therefore $L^c$ belongs to the union defining BPP.

**Key facts.** `Randomized.compl_mem_BPTIME`.
