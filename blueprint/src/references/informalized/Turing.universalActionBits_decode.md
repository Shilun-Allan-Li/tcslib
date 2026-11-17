<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalBlock.lean :: Turing.universalActionBits_decode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding the Eight Action Bits

**Claim.** The eight bits encoding a one-work-tape action recover its input movement, work-tape write and movement, and optional output symbol.

**Proof.** The encoding records the input movement in bits $0,1$, the work-tape write instruction in bits $2,3$, the work movement in bits $4,5$, and output presence and value in bits $6,7$. Check each field by cases on the value it encodes. The three possible movements (negative, zero, positive) decode to themselves under the two-bit sign code. The possible write instructions—no write, erase, or write either Boolean symbol—decode to themselves under the write code. The same sign check applies to the work movement. Finally, an absent output decodes to none, while either present Boolean output decodes to that symbol. Hence all four fields are recovered.
