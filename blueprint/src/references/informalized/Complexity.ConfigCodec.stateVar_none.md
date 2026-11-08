<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.ConfigCodec.stateVar_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Index of the halting-state variable

**Claim.** For every natural number $n$, the variable assigned to the absent state is the state offset $2n+2$.

**Proof.** By definition, the variable index is the state offset plus the state index. The absent state has state index $0$, so the variable index is exactly the state offset, namely $2n+2$.
