<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clRepeat_call -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Relocated Clean Call

**Claim.** A clean call of the source machine, starting in entry with state word $s$ and ending after exactly $t$ steps in exit with state word $s'$, is reproduced by the repetition controller from its begin state; the clock contents and cursor are preserved.

**Proof.** Represent the source call configuration as the source machine's configuration with its state word, and place its tapes in the repetition controller's source-tape slots while retaining the clock on the extra tape. The frame identity identifies this placed configuration with the controller configuration in its lifted entry state (`Complexity.clRepeat_frame`). The controller's first step, in its begin phase, performs the source transition on those slots; the tape-placement correspondence says that applying the placed action is exactly placing the result of the source action (`Complexity.clPlaced_apply`). From then on, the controller follows the source run. The no-intermediate-exit hypothesis ensures that each state before the final step is a state on which the controller continues to simulate the source transition, rather than taking its exit branch. The run-preservation theorem for placed machines therefore carries the simulation through the remaining $t-1$ steps (`Complexity.clPlaced_run`). The source run after its first step reaches the stated exit configuration after $t-1$ further steps, by the successor-time identity for runs (`Turing.MultiTapeTM.runFrom_succ_eq_step`). Placing that final source configuration again identifies it with the lifted exit configuration, with the same clock contents and cursor (`Complexity.clRepeat_frame`).

**Key facts.** `Complexity.clRepeat_frame`, `Complexity.clPlaced_apply`, `Complexity.clPlaced_run`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
