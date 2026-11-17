<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codec_posCode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a position code

**Claim.** For every natural number $s$ and every $j\in\{0,1,\ldots,2s\}$, the position code with bound $s$ of the integer $j-s$ is $j$.

**Proof.** Both sides are elements of the same finite interval, so it suffices to compare their values. By definition, the value of the position code is $\min((j-s+s).\mathrm{toNat},2s)$. Since $j-s+s=j$ and $j\le 2s$, this minimum is $j$. The bound needed to form the finite value follows from the same inequality.
