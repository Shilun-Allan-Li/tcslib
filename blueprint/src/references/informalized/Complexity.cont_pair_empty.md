<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_pair_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection of the empty input

**Claim.** On the empty input, the pair-loader machine halts after one step with output $[0]$.

**Proof.** The computation-in-time equivalence reduces the claim to checking that the configuration reached after one step is halting and has output $[0]$ (`Turing.FinTM.computesInTime_iff`). Express the one-step run as a step from the initial configuration using the successor-run identity (`Turing.MultiTapeTM.runFrom_succ_eq_step`). At the empty input the initial state is parser state $0$ and the input symbol is absent. The defining transition for this case halts and emits false, so the resulting output is the singleton word $[0]$; the required state and output conditions follow.

**Key facts.** `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
