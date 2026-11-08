<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Machine.lean :: Complexity.LogProg.ExpBFS.St.toV_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-State Register Vector

**Claim.** The constant function taking value $0$ on the indices equals the register vector of the zero state.

**Proof.** Two functions on the 17 indices are equal if they agree at every index. At each index, the constant function has value $0$, and the corresponding register of the zero state is also $0$ by its definition. Thus the functions agree at all 17 indices, proving the equality.
