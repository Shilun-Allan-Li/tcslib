<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Run.lean :: Complexity.LogProg.SavitchARM.sh_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Registers in the Shift Routine

**Claim.** At every shift-routine site, the loop counter is distinct from both the site register and the scratch register, and the site register is distinct from the scratch register.

**Proof.** There are three shift sites: the code-bound register, the endpoint-stack register, and the pop-stack register. Their register indices are respectively $9$, $14$, and $17$, while the loop counter and scratch registers have indices $6$ and $5$. Each asserted inequality follows by comparing these indices. The Boolean parameter at the endpoint-stack and pop-stack sites does not change which register the site uses.
