<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.AgreeShift.stepWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Shifted Agreement After One Choice

**Claim.** If configurations $c,c'$ agree with shift $d$ and radius $r+1$, then after one step under the same choice bit $b$, they agree with shift $d$ and radius $r$.

**Proof.** Unpack the agreement into equality of states, input-head positions, and outputs, the prescribed relation between work-tape head positions, and agreement of tape contents to the left of the radius boundary. If $c$ is halted, equality of states makes $c'$ halted too, and both steps leave the configurations unchanged (`stepWith_of_halt`). The tape agreement at radius $r$ follows from the original agreement at radius $r+1$, since its range condition is weaker. If $c$ is in a state $q$, then $c'$ is in the same state. The old tape contents under their respective head positions agree: this follows by applying the tape agreement at the head cell, which lies within the radius-$r+1$ region. Thus both configurations read the same work symbols; their input symbols also agree because their input-head positions coincide. They therefore use the same transition action. Applying that action preserves the state relation, input-head relation, output relation, and head-position shift. For tape contents, the action either leaves the tape unchanged or writes at the old head cell. A queried cell away from that head retains the original agreement; at the head cell, both sides receive the same write. Finally, each head moves by at most one, since its movement sign is in $\{-1,0,1\}$ (`signType_bounds`). Consequently every cell in the new radius-$r$ region lies in the old radius-$(r+1)$ region, so the needed original tape agreement is available.

**Key facts.** `Turing.NDTM.stepWith_of_halt`, `Turing.signType_bounds`.
