<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.skipTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Forward Skip over a Word

**Claim.** Under the stated tape-content hypothesis, the skipping machine reaches the done phase after $|w|+1$ steps with tape head $i$ at $d_i+|w|+1$, is not done at any earlier time, and keeps its work-tape heads within the stated bounds throughout.

**Proof.** Index the configurations by the distance $r$ moved to the right from the initial head position. The indexed configuration has state run and tape head $i$ at $d_i+r$; at $r=0$ it is exactly $d$. By the catalog seek step fact (`Turing.catalog_seek_step`), each indexed transition is determined by the scanned tape symbol. For every $r<|w|$, the hypothesis identifies that symbol with the $r$th symbol of $w$, so the machine stays in the run phase and advances one cell. At $r=|w|$, the tape hypothesis gives a blank, so the next step enters the done phase and moves the head to $d_i+|w|+1$.

The done configuration is stationary: its transition is an input-only action with zero input movement, and the zero-movement fact fixes the input head (`Turing.step_of_inputMoveAction`, `Turing.moveInputPos_zero`). The catalog pass contract (`Turing.catalog_pass_contract`), applied to the indexed path of length $|w|$, gives the claimed final configuration, non-done status at every earlier time, and head-position bounds at every time through the exit. The indexed initial and exit configurations are respectively $d$ and the stated done configuration, so the contract yields all three conclusions for the run from $d$.

**Key facts.** `Turing.catalog_seek_step`, `Turing.step_of_inputMoveAction`, `Turing.moveInputPos_zero`, `Turing.catalog_pass_contract`.
