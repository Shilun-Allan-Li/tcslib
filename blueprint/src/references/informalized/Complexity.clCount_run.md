<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clCount_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed In-Place Increment

**Claim.** For every bit-list input, valid input-head position, and bit list $w$, running the increment machine for exactly $2\operatorname{carry}(w)+2$ steps from carry control with head at zero and tape holding $w$ ends in return control with head at zero, tape holding the increment of $w$, and unchanged input head and empty output.

**Proof.** First apply the carry-phase result with empty prefix. After $\operatorname{carry}(w)+1$ steps, the machine is in rewind control, the tape holds $\operatorname{inc}(w)$, and the head is at $\operatorname{carry}(w)-1$ (`Complexity.clCount_carry`). Split the full duration into two blocks of $\operatorname{carry}(w)+1$ steps. The run-addition law says that the second block starts from the configuration reached by the first (`Turing.MultiTapeTM.runFrom_add`). Apply the rewind result to this second block, taking $j=\operatorname{carry}(w)$ and the tape to be $\operatorname{inc}(w)$. Its side condition $j\le |\operatorname{inc}(w)|$ follows from the carry-length bound (`Complexity.clCountInc_length`). Rewinding reaches return control and head position zero without changing the tape or output. The two equal-duration blocks sum to the claimed duration.

**Key facts.** `Complexity.clCountInc_length`, `Complexity.clCount_carry`, `Complexity.clCount_rewind`, `Turing.MultiTapeTM.runFrom_add`.
