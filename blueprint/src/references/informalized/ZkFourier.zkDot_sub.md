<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkFourier.lean :: ZkFourier.zkDot_sub -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subtraction in the left argument

**Claim.** For vectors $s,t,x\in\mathbb{Z}_k^n$, the dot product satisfies $(s-t)\cdot x=s\cdot x-t\cdot x$.

**Proof.** At each coordinate $i$, scalar distributivity gives $(s_i-t_i)x_i=s_ix_i-t_ix_i$. Summing these coordinatewise identities over the finite index set and distributing the finite sum over subtraction yields the asserted equality.
