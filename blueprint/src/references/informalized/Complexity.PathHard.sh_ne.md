<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathHardMachine.lean :: Complexity.PathHard.sh_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Shift Registers

**Claim.** For each of the four shift operations, the counter register, the register being shifted, and the scratch register are pairwise distinct.

**Proof.** There are four cases, corresponding to the four shift operations. In each case the shifted register is one of $r_N,r_M,r_K,r_T$, respectively, and these are distinct from the counter register $r_C$ and the scratch register $r_Z$; the shifted register is also distinct from $r_Z$. Thus all three pairwise inequalities hold in every case.
