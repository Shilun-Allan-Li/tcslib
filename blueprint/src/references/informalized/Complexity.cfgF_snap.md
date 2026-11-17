<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PSubsetPPolyConfigStep.lean :: Complexity.cfgF_snap -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Snapshot Update Rule

**Claim.** Given the stated time, acceptance, input-symbol, work-tape-symbol, and previous-snapshot bits, the snapshot update rule produces the snapshot encoding at time $t$ followed by the acceptance indicator at time $t$.

**Proof.** First the supplied presence and value bits reconstruct the current input symbol and each current work-tape symbol as optional Booleans (`Complexity.CfgTableau.optOf_isSome_getD`). Split on the time. At $t=0$, the first bit selects initialization: the updated state is the machine's initial state, the reconstructed tape symbols and input symbol are the initialized configuration data, and the acceptance indicator is false because there is no earlier time at which acceptance could have occurred. These are exactly the time-zero snapshot and acceptance bit. For $t>0$, write $t=s+1$. The previous-snapshot field decodes to the snapshot at time $s$. Its successor state is the state at time $s+1$ by the state component of `snapshotAt_state_succ`; the other snapshot components are already supplied by the current symbol bits. Hence the assembled snapshot is the time-$t$ snapshot. Finally, `tableauAccepted_succ` states that acceptance through time $s+1$ is the disjunction of acceptance through time $s$ and an accepting output emitted from the snapshot at time $s$. The hypotheses supply the former bit and the decoded snapshot supplies the latter, so the rule's final bit is precisely the acceptance indicator at time $t$.

**Key facts.** `Complexity.CfgTableau.optOf_isSome_getD`, `Complexity.snapshotAt_state_succ`, `Complexity.tableauAccepted_succ`.
