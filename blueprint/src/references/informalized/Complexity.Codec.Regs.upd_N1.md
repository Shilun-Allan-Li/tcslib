<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Regs.lean :: Complexity.Codec.Regs.upd_N1 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the N1 register

**Claim.** Changing the value at index $5$ in the sequence of register values of $R$ to $v$ gives the sequence of register values of the record obtained by replacing $R$’s $N1$ register with $v$.

**Proof.** To prove equality of the two sequences, compare their values at an arbitrary index. Since the index ranges over the finite set of $21$ positions, check each position. At index $5$, the update gives $v$, matching the record with $N1$ replaced by $v$; at every other position, both sequences retain the corresponding register value of $R$. Thus the sequences agree at every index and are equal.
