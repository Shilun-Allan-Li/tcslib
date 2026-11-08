<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/PCPPConstructions.lean :: FABL.singletonTrueString_isOddWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Odd Weight of a Singleton String

**Claim.** For each coordinate $i$, the Boolean string that is true only at $i$ has odd Hamming weight.

**Proof.** The parity of the string is the sum, in $\mathbb{F}_2$, of the encoded values at all coordinates. At every coordinate other than $i$, the singleton string is false, so its encoded value is zero. The sum therefore reduces to the value at $i$, where the string is true and its encoding is $1$. Thus the parity is $1$, which is precisely odd weight.
