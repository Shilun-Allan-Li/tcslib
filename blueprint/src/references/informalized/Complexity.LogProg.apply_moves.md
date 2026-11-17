<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/CallReturn.lean :: Complexity.LogProg.apply_moves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register-Only Head Moves

**Claim.** An action that moves the input head by $mv_I$, moves each register head $r$ by $f(r)$, leaves tape contents unchanged, and leaves decider heads fixed changes the state to $st'$ and otherwise has exactly the stated effects.

**Proof.** Compare the fields of the resulting configuration. Its state is $st'$ and its input position is the clamped move of the old position. Each register instruction has no write component, so all register tapes stay unchanged, while register head $r$ moves from $rp(r)$ to $rp(r)+f(r)$. Each decider instruction is idle, leaving its tape and head position unchanged. The action emits nothing, so the output is unchanged.
