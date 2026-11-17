<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.FinNDTM.coinBranch_stepWith₁ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step preserves the second branch

**Claim.** Taking one step of the combined machine from a configuration of $N_1$ embedded in the second branch gives the embedding of the configuration obtained by taking the same choice step of $N_1$.

**Proof.** First consider a halted configuration: the combined configuration is halted as well, and a step leaves each configuration unchanged (`stepWith_of_halt`). Otherwise let $q$ be the original state. Its embedded state is tagged in the second branch; the input symbol is unchanged, and reading the combined machine's work tapes in the second block recovers exactly the work-head symbols of $N_1$. Hence its transition uses the same action as $N_1$. The combined action places the action's tape effects in the second block, leaving the first block blank and stationary, and tags its successor state in the second branch. The input position and output are preserved in the same way, so each component is the embedding of the configuration after $N_1$'s step. The active-state transitions are characterized by `stepWith_of_state`.

**Key facts.** `Turing.NDTM.stepWith_of_halt`, `Turing.NDTM.stepWith_of_state`.
