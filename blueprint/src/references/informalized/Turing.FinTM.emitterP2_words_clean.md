<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_words_clean -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Host Word Layout

**Claim.** With both bank words empty, the host layout equals the standard word assignment for $s$ on $k+l+1$ tapes.

**Proof.** Check the functions at each tape index. At the initial index, both assign $s$. At every index in either bank, the corresponding standard assignment is empty because its bank word is empty; the standard assignment for $s$ is empty at every nonzero index as well. Thus the functions agree at every index.
