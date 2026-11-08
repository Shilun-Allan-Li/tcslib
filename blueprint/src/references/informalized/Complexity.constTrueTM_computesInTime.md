<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ZeroSpace.lean :: Complexity.constTrueTM_computesInTime -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Constant-True Computation

**Claim.** The fixed machine that always outputs true halts after exactly one step on every finite Boolean input and has output $[\mathrm{true}]$.

**Proof.** The characterization of time computation says that a machine computes the specified output in time $t$ exactly when its run at time $t$ is halted and has that output (`Turing.FinTM.computesInTime_iff`). For the fixed constant-true machine at time one, the run state is none and its output is $[\mathrm{true}]$, by the defining computation of that machine. These two equalities establish the claim.

**Key facts.** `Turing.FinTM.computesInTime_iff`.
