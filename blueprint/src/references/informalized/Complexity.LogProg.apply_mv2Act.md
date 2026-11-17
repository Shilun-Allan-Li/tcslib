<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.apply_mv2Act -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simultaneous Register Movement

**Claim.** Applying the action that moves both designated register heads by $mv$ to the configuration with state $s$ and both designated head positions set to $k$ gives state $s'$, leaves the input position, tapes, and output unchanged, and sets both designated positions to $k+mv$.

**Proof.** The action sets the state to $s'$ and has zero input movement, so the input position is unchanged (`Turing.moveInputPos_zero`). Every tape instruction has no write component, hence all tape contents are preserved; the output is likewise unchanged. For each register index, its head moves by $mv$ exactly when it equals either designated index, and otherwise moves by zero. Thus each designated head, including when the two indices coincide, moves from $k$ to $k+mv$, while all other heads retain their previous positions.

**Key facts.** `Turing.moveInputPos_zero`.
