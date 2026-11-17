<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_first_anchor -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Visit to an Anchor State

**Claim.** If the stopped machine, which remains stationary in state $q_a$, is in $q_a$ at time $T$, then the original machine has a first time $t\le T$ with the same configuration as the stopped machine at time $T$, and it was not in $q_a$ at any earlier time.

**Proof.** Choose $t$ to be the least time at which the stopped machine is in state $q_a$. Existence follows from the visit at time $T$, and minimality gives $t\le T$ and excludes $q_a$ at every earlier time. From time $t$ onward the stopped machine stays at exactly the same configuration: the transition in state $q_a$ is stationary and silent (`Complexity.enumCont_absorb`). Thus its configuration at time $T$ equals its configuration at time $t$; the run-addition law (`Turing.MultiTapeTM.runFrom_add`) expresses this continuation. Up to time $t$, the original and stopped machines agree because their transitions coincide away from $q_a$ (`Complexity.enumCont_agree_run`), and the stopped run has not visited $q_a$ before $t$. Hence the original machine at time $t$ equals the stopped machine at time $T$, with no earlier visit to $q_a$.

**Key facts.** `Complexity.enumCont_absorb`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.enumCont_agree_run`.
