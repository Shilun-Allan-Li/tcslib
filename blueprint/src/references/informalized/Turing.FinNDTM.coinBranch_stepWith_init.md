<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.FinNDTM.coinBranch_stepWith_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial step selects a branch

**Claim.** One step of the combined machine from its initial configuration, using choice $b$, gives the embedded initial configuration of $N_1$ if $b=1$ and of $N_0$ if $b=0$.

**Proof.** Split into the two possible values of $b$. In either case, the combined machine starts in its special state with no active branch, so its transition selects the initial state of the corresponding machine. The resulting state is that selected initial state tagged with the appropriate branch. The transition leaves the work tapes blank and their heads at the origin, leaves the output empty, and keeps the initial input-head position. Thus every component of the resulting configuration agrees with the corresponding embedded initial configuration.
