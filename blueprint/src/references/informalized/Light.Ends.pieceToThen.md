<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.pieceToThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential Composition with Refreshed Locals

**Claim.** If $s_1$ executes from the frame of $l$ within $T_1$ to a state satisfying $R$, and $s_2$ executes from the refreshed frame within $T-T_1$ to $Q$, then $s_1;s_2$ executes within $T$ to $Q$, provided all locals assigned by $s_1$ are in $xs$ and $T_1\le T$.

**Proof.** Apply `Light.Ends.pieceTo` to the first execution. Because every local assigned by $s_1$ is among the refreshed indices, its final locals are represented by refreshing the original frame from those final locals; the given continuation hypothesis therefore supplies an execution of $s_2$ within $T-T_1$ to $Q$ from each resulting state. This gives the first statement an execution whose postcondition is that such a second execution exists. Apply the sequential-composition principle `Light.Ends.next` with budget split $T_1$ and $T$ to join the two executions.

**Key facts.** `Light.Ends.next`, `Light.Ends.pieceTo`.
