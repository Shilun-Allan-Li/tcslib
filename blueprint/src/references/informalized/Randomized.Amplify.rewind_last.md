<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplify.lean :: Randomized.Amplify.rewind_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final Rewind Step

**Claim.** At the final rewind index, either possible first choice makes the amplified machine finish immediately, appending the decision value at counter $c$ and entering a halted state; all subsequent choices leave that same configuration unchanged.

**Proof.** Because $j$ is not less than $r$, the rewind transition takes the final-index branch. For either Boolean choice, it performs an idle action that leaves the input head fixed, appends $\mathrm{dec}(c)$ to the output, and sets the state to halted. The action’s effect is given by the idle-action description (`idle_apply`), with a zero input movement leaving the position unchanged (`Turing.moveInputPos_zero`). Thus both first choices produce exactly `finish dec C c`. Running the rest of $w$ from that halted configuration changes nothing (`Turing.NDTM.runWith_of_halt`), proving both equalities.

**Key facts.** `Randomized.Amplify.step_of_state`, `Randomized.Amplify.idle_apply`, `Turing.moveInputPos_zero`, `Turing.NDTM.runWith_cons`, `Turing.NDTM.runWith_of_halt`.
