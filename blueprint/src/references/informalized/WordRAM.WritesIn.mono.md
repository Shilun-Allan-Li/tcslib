<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/WordRAM/Steps.lean :: WordRAM.WritesIn.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Write Restrictions

**Claim.** If every address written by an instruction, according to the condition defining writes in $s$, lies in $s$, then it also satisfies the corresponding condition for any set $t$ containing $s$.

**Proof.** Split into the possible instruction forms. For instructions whose condition says that the destination address lies in the set, the given address membership in $s$ implies membership in $t$ because $s\subseteq t$. For a store, the condition is false, so the premise cannot hold. For instructions whose condition is automatically true, it remains true for $t$ as well.
