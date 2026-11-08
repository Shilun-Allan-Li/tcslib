<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arBuffer_full -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complete read buffer

**Claim.** After $N+1$ reading steps, the buffer is the complete coded block $E(r(i))$ on every tape $i$.

**Proof.** Fix a tape $i$ and block position $b\in\mathrm{Fin}(N+1)$. At reading depth $N+1$, the buffer definition retains the coded entry precisely when $b<N+1$. This inequality holds because $b$ belongs to that finite range. Hence the entry is $E(r(i))(b)$, which is exactly the corresponding entry of the complete coded block. Since this holds for every tape and position, the functions agree.
