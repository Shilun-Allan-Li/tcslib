<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInPWords.lean :: Randomized.BPLInP.iterate_codeStep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Iterated code step

**Claim.** Applying the code update $i$ times to the pairing of two empty bit strings yields the pairing of the binary representation of $i$ with the encoded list of binary representations of $0,1,\ldots,i-1$.

**Proof.** Proceed by induction on $i$. At $i=0$, zero iterations leave the initial pairing unchanged, which is the claimed encoding for the empty range. For the successor step, assume the formula at $i$. One more update adds one to the first encoded natural number: the binary-value identity `bitsVal_bits` confirms that decoding and re-encoding the binary representation gives the representation of $i+1$. The update also appends the encoding of the previous first component, namely the binary representation of $i$, to the stored list. The range decomposition into the first $i$ indices followed by $i$ (`List.range_succ`), together with the singleton-append rule for `encWords` (`encWords_append_singleton`), identifies the resulting stored list as the encodings for $0$ through $i$. This is the required formula at $i+1$.

**Key facts.** `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.encWords_append_singleton`.
