<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.beq_mem_P -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Decidability of Encoded Equality

**Claim.** The language of bit strings whose decoded components have equal binary values is in polynomial time, where invalid encodings yield empty decoded components.

**Proof.** The Boolean test comparing the binary values of the two decoded components is computable in polynomial time ($\texttt{polyTimeComputable\_beq}$). The general test-to-language result says that the set of inputs on which a polynomial-time Boolean test returns true belongs to $\mathrm{P}$ ($\texttt{mem\_P\_of\_test}$). Applying it to this equality test proves the claim.

**Key facts.** `Complexity.BinArith.polyTimeComputable_beq`, `Complexity.mem_P_of_test`.
