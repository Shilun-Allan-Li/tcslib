<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_nonempty_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Preserved Under State Renaming

**Claim.** For any configuration $c$ of $M$ and any $t\in\mathbb N$, running the nonempty-input guard for $t$ steps from the configuration obtained by renaming the states of $c$ gives the state-renamed configuration reached by running $M$ from $c$ for $t$ steps.

**Proof.** The proof uses the run-commutation principle: if a map on configurations carries each single step of one machine to the corresponding single step of another, then it carries every finite run to the corresponding run (`runFrom_comm_of_step`). Take this map to rename each state by the right injection into the guard’s state type, leaving all other configuration fields unchanged. To verify the required one-step identity, split according to whether the current state is halted. In the halted case both machines leave the configuration unchanged. In the live-state case the renamed state lies in the simulation branch of the guard, whose transition is exactly the transition of $M$ with its successor state renamed; applying it therefore agrees with first stepping in $M$ and then renaming. The commutation principle now gives the claimed equality for every $t$.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`.
