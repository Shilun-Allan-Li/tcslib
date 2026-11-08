<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountRegs.lean :: Complexity.LogProg.ISCount.St.toV_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero state vector

**Claim.** The vector associated with the zero state is the constant function on the 17 register indices with value $0$.

**Proof.** Two functions on the register indices are equal if they agree at every index. Fix an index and consider its possible values in the finite type of 17 indices. In each case, the corresponding coordinate of the zero state is $0$, so it agrees with the constant-zero function. Thus the two functions are equal.
