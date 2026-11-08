<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.FinNDTM.coinBranch_stepWith₀ -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step preserves the first branch

**Claim.** Taking one step of the combined machine from a configuration of $N_0$ embedded in the first branch gives the embedding of the configuration obtained by taking the same choice step of $N_0$.

**Proof.** Split according to whether the state of the original configuration is halted. If it is halted, both machines leave their configurations unchanged, by the fact that a step from a halted configuration does nothing (`stepWith_of_halt`). Otherwise write its state as $q$. The embedded state is then tagged as belonging to the first branch, and its input symbol is unchanged. Reading the combined machine's work tapes at the indices for the first branch gives exactly the original work-head symbols. Consequently the combined transition uses the same action as $N_0$; that action is embedded by tagging its successor state in the first branch and placing its work-tape effects in the first block, while the other block remains blank and stationary. The input position, output, and all work-tape contents and head positions therefore agree componentwise with the embedded result. For the active-state case, the step is indeed given by applying the transition action (`stepWith_of_state`).

**Key facts.** `Turing.NDTM.stepWith_of_halt`, `Turing.NDTM.stepWith_of_state`.
