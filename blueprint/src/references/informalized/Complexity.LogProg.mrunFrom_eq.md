<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/MARMCompile.lean :: Complexity.LogProg.mrunFrom_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulation with Unused Memory

**Claim.** If the deterministic compiled run has no selected memory instruction at any state it visits before time $T$, then through every time $t\le T$ the memory-augmented compiled run agrees with that deterministic run after attaching the same memory tape and head position.

**Proof.** Use induction on time. At time zero, both runs begin at the same configuration, with the memory tape and head attached, so the equality holds. For the successor step, let $t+1\le T$ and use the induction hypothesis at time $t$. The hypothesis about the run says that if its configuration at time $t$ has a state, the memory selector returns no instruction there. The one-step simulation fact for states with no selected memory instruction (`mcompileTM_step`) therefore says that stepping the memory-augmented machine from the attached configuration gives exactly the attachment of the deterministic machine's next configuration. The defining recursion for runs identifies these next configurations with the runs at time $t+1$, proving the claim.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Complexity.LogProg.mcompileTM_step`.
