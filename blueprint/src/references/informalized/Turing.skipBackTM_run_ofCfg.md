<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.skipBackTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Backward Skip over a Word

**Claim.** Under the stated tape-content hypothesis, the skipping machine reaches the done phase after $|u|+3$ steps with tape head $i$ at $d_i-|u|-1$, is not done at any earlier time, and keeps its work-tape heads within the stated bounds throughout.

**Proof.** Track the machine along configurations indexed by $r$, with state run at $r=0$, gap at $r=1$, and back thereafter, while tape $i$'s head is at $d_i-r$. The initial indexed configuration is $d$. The one-step description of these indexed configurations is supplied by the catalog seek step fact (`Turing.catalog_seek_step`).

The first step moves left into the gap phase, and the second moves left into the back phase. For each subsequent indexed position before the exit, the tape hypothesis says that the scanned cell contains the corresponding symbol of $u$. Thus the machine remains in the back phase and moves left one cell. At the final position, corresponding to offset $p=-1$, the hypothesis makes the scanned cell blank; the transition moves right and enters the done phase. This places the head at $d_i-|u|-1$. The resulting done configuration is stationary: its transition is an input-only action with zero input movement, so the input head stays fixed by the zero-movement fact (`Turing.step_of_inputMoveAction`, `Turing.moveInputPos_zero`).

Apply the catalog pass contract (`Turing.catalog_pass_contract`) to this sequence, taking its length parameter to be $|u|+2$. It gives the final configuration after one further indexed step, excludes the done phase at every earlier time, and carries the head-position bounds for all intermediate configurations and the exit configuration. The initial identity and the definition of the final configuration identify these conclusions with the asserted run from $d$.

**Key facts.** `Turing.catalog_seek_step`, `Turing.step_of_inputMoveAction`, `Turing.moveInputPos_zero`, `Turing.catalog_pass_contract`.
