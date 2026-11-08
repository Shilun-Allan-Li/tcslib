<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_Q1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Q1 register

**Claim.** Changing the value at index $15$ in the sequence of register values of $R$ to $v$ gives the sequence of register values of the record obtained by replacing $R$’s $Q1$ register with $v$.

**Proof.** To prove equality of the two sequences, compare their values at an arbitrary index. Since the index ranges over the finite set of $21$ positions, check each position. At index $15$, the update gives $v$, matching the record with $Q1$ replaced by $v$; at every other position, both sequences retain the corresponding register value of $R$. Thus the sequences agree at every index and are equal.
