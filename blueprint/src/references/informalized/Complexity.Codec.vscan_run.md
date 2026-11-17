<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean :: Complexity.Codec.vscan_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of the configuration scan

**Claim.** Under the stated shape, register bounds, register values, and input-length condition, the codec program reaches a completed scan whose state is the scan of the first $W_N(2s+1)$ bits of $w$, while keeping its registers within the prescribed bound and ending with $Q_1=Q_2=E$ at their original value.

**Proof.** Write $B$ for the register bound and let $u$ be the prefix of $w$ of length $W_N(2s+1)$. The relation between the given values of $A$ and $E$ is $E=A+2|u|$.

1. The program first clears $Q_1$, then clears $Q_2$. Next it copies $A$ into $Q_1$ and copies $A$ into $Q_2$. These are single register-copy operations (`cp_run`); the initial clear steps are single transitions. The supplied register bound and the fact that copying does not increase a register beyond its source ensure the guard bound at each stage (`Regs.Bd.val_le`, `gd_of`).

2. The scan routine now reads $|u|$ paired positions from the input, using $Q_1$ and $Q_2$ as position counters. The pair-encoding address formula (`getD_w`) and the hypothesis that $y$ encodes $x$ and then $w$ show that each read retrieves the corresponding bit of $u$ in both streams. The routine's execution lemma (`v_run`) therefore yields the scan state obtained by folding the scan transition over the paired prefix. Since the streams are both $u$, this is exactly the required scan of $u$.

3. At completion, the routine advances both counters by $2|u|$. Hence both equal $A+2|u|=E$. Rewriting the resulting register assignment as the original assignment with $Q_1$ and $Q_2$ set to $E$ gives the stated endpoint. The intermediate executions compose by transitivity of reachability (`Reach.trans`), and `Reach.cast` identifies the routine's updated-register form with the stated endpoint.

**Key facts.** `Complexity.Codec.Regs.Bd.val_le`, `Complexity.Codec.gd_of`, `Complexity.Codec.Reach.single'`, `Complexity.Codec.cp_run`, `Complexity.Codec.getD_w`, `Complexity.Codec.v_run`, `Complexity.Codec.Reach.cast`, `Complexity.Codec.Reach.trans`.
