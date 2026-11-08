<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Walk.lean :: Complexity.LogProg.TQBFARM.cont -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariance Under Equal States

**Claim.** If two states are equal, any bounded guarded reachability from the second state also holds from the first state.

**Proof.** Since $st=st'$, their register vectors are equal. Substituting this equality into the given reachability witness yields the same run and the same endpoint, now with initial register vector $st.toV$.
