<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.bitsVal_pow2W -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value of a Padded Power

**Claim.** For natural numbers $B,e$ and a Boolean list $x$, the binary value of the word formed by $B(|x|+1)^e$ zeros followed by a one is $2^{B(|x|+1)^e}$.

**Proof.** The zero-generating word is a list of false bits whose length is the length of its input (`Randomized.BPLInP.zerosW_eq`). Thus the word in question consists of $n=B(|x|+1)^e$ zeros followed by one. Induct on $n$. At $n=0$, the word is the single true bit, with binary value $1=2^0$. In the successor case, adding one leading false bit doubles the binary value of the remaining word; by induction this is $2\cdot 2^n=2^{n+1}$.

**Key facts.** `Randomized.BPLInP.zerosW_eq`.
