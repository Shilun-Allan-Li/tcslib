<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Round.of_cut -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Round from an Intermediate-State Cut

**Claim.** If a run starts in state $a$, has positive duration, avoids both $a$ and $e$ at every strictly intermediate positive time, and ends in state $a$ or $e$, then it forms a round with escape set $\{\mathrm{some}(e)\}$ and the everywhere-true head-position property.

**Proof.** The starting-state and positive-duration requirements are assumed, and the endpoint is the run at time $t$ by definition. If its state is $a$, it lies in the required endpoint set directly; if its state is $e$, it lies there by membership of $\mathrm{some}(e)$ in the escape set. At a strictly intermediate time, the cut hypothesis gives a state $s$ different from both $a$ and $e$. Consequently the optional state is neither halted nor the anchor nor in the escape set, so it is outside the round-stop set by the characterization `Turing.not_mem_roundStop`. Finally, the head-position condition holds at every time because the property is identically true.

**Key facts.** `Turing.not_mem_roundStop`.
