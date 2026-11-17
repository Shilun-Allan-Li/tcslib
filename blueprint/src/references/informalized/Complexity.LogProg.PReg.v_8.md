<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/PathWalkMachine.lean :: Complexity.LogProg.PReg.v_8 -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guessed-Next-Vertex Register

**Claim.** For a register state with values $(p,n,a,b,s,t,tmp,st,nx)$ in registers $0$ through $8$, the value in register $8$ is $nx$.

**Proof.** By the definition of the register valuation, its entries are listed in register order, with $nx$ as the ninth entry. Evaluating that list at index $8$ therefore gives $nx$.
