<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/SavitchARM/Machine.lean :: Complexity.LogProg.SavitchARM.St.upd_C -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating the Loop Counter

**Claim.** For any register state and natural number $k$, replacing the loop-counter coordinate of its register vector by $k$ gives the register vector of the state with loop counter set to $k$.

**Proof.** Compare the two functions at each register index. At the loop-counter index $r_C=6$, updating the vector assigns $k$, which is also the value of the vector for the state whose loop counter is set to $k$. At every other index, the update leaves the original coordinate unchanged, and changing the state’s loop counter leaves those other coordinates unchanged as well. Hence the functions agree at every index.
