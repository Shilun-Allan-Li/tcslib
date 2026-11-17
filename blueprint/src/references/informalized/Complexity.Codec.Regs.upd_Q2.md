<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_Q2 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Q2 register

**Claim.** Changing the value at index $16$ in the sequence of register values of $R$ to $v$ gives the sequence of register values of the record obtained by replacing $R$’s $Q2$ register with $v$.

**Proof.** To prove equality of the two sequences, compare their values at an arbitrary index. Since the index ranges over the finite set of $21$ positions, check each position. At index $16$, the update gives $v$, matching the record with $Q2$ replaced by $v$; at every other position, both sequences retain the corresponding register value of $R$. Thus the sequences agree at every index and are equal.
