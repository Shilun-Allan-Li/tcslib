<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_move_stay -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Silent stationary input move

**Claim.** Applying the silent action that leaves the input head stationary, moves the work head by $e$, and enters state $q'$ produces the stated configuration.

**Proof.** The action sets the state to $q'$ and leaves the input head in place because its input movement is zero. It makes no work-tape write, while moving the work head from $h$ to $h+e$. Since it emits no symbol, the output remains $o$. Thus every component agrees with the claimed configuration.
