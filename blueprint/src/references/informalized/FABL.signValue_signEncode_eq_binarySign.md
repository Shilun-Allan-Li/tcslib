<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/BLR.lean :: FABL.signValue_signEncode_eq_binarySign -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sign Encoding and Binary Character

**Claim.** For every $b\in\mathbb{Z}/2\mathbb{Z}$, the real value of $(-1)^b$ equals the binary character that is $1$ at $0$ and $-1$ at $1$.

**Proof.** Represent $b$ by its canonical value $b.\mathrm{val}\in\{0,1\}$. The power of the sign $-1$ by $b$ is the same as its power by this representative. Casting that integer power to the reals preserves multiplication and powers, so its real value is $(-1)^{b.\mathrm{val}}$. By the definition of the binary character, this is precisely its value at $b$.
