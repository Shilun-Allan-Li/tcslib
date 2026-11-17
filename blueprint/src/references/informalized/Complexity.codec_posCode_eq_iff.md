<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codec_posCode_eq_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of a position code

**Claim.** If $z$ is an integer with $|z|\le s$ and $j\in\{0,1,\ldots,2s\}$, then the position code of $z$ with bound $s$ equals $j$ if and only if $z=j-s$.

**Proof.** For the forward implication, the bound $|j-s|\le s$ follows from $0\le j\le 2s$. The given bound on $z$ and this bound on $j-s$ allow us to use injectivity of the position code on the interval $[-s,s]$ (the fact `posCode_injOn`). The decoding identity `codec_posCode` says that the code of $j-s$ is $j$; combining it with the assumed equality of codes gives $z=j-s$. Conversely, if $z=j-s$, the same decoding identity directly gives that its code is $j$.

**Key facts.** `Turing.MultiTapeTM.ConfigCount.posCode_injOn`, `Complexity.codec_posCode`.
