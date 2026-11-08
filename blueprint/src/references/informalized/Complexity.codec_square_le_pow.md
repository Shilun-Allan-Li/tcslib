<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codec_square_le_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic bound by an exponential

**Claim.** For every natural number $C\ge4$, one has $C^2\le2^C$.

**Proof.** Write $C=4+t$ for a natural number $t$, and induct on $t$. At $t=0$, the assertion is $16\le16$. For the successor step, assume $(4+t)^2\le2^{4+t}$. A direct expansion, using $t\ge0$, gives $(4+(t+1))^2\le2(4+t)^2$. The induction hypothesis then bounds this by $2\cdot2^{4+t}=2^{4+(t+1)}$, proving the next case.
