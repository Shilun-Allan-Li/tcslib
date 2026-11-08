<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Frames.lean :: Light.Ends.pieceTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution with Refreshed Local Variables

**Claim.** An execution from the zero-padded frame of $l$, bounded by $T_1$ and ending in $R$, yields an execution bounded by $T$ ending in $Q$ at the frame obtained by refreshing the indices in $xs$, provided every local assigned by $s$ occurs in $xs$ and $T_1\le T$.

**Proof.** Use `Light.Ends.keeping` to retain the original execution and its postcondition while also recording that every local not assigned by $s$ keeps its initial value. For any index outside $xs$, the assignment hypothesis ensures it is not assigned by $s$, so this preservation fact applies. Thus the final local function agrees with the original frame outside $xs$; the characterization `Light.LocalsBut.eq_frame` identifies that function with the frame obtained by refreshing the entries in $xs$ from the final locals. The assumed implication from $R$ to $Q$ for precisely this refreshed frame now gives the desired postcondition. Finally, `Light.Ends.mono` enlarges the cost bound from $T_1$ to $T$.

**Key facts.** `Light.Ends.keeping`, `Light.LocalsBut.eq_frame`, `Light.Ends.mono`.
