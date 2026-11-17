<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/ParsePlain.lean :: Complexity.LogProg.validPlain_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of valid plain words

**Claim.** A Boolean word is a valid plain encoding if and only if its initial run of ones has even length, the next two bits are $01$, and the remaining suffix is canonical.

**Proof.** For a valid encoding, write the word as the encoding of $n$ ones and a canonical suffix $w$. The initial run has length $2n$ (`dbl_replicate` and the pair-encoding identity `pairEncode_eq_dbl`), and the next two bits are the separator $01$. Dropping this prefix recovers $w$, so the suffix is canonical.

Conversely, assume the stated bit and suffix conditions. Every position before $tRun(y)$ contains a one (`getElem?_lt_tRun`), so the first $tRun(y)$ bits are exactly a string of ones. The next two bits are $01$; the length bound $tRun(y)\le |y|$ (`tRun_le`) and these two present bits ensure the prefix is in range. Splitting the list at that prefix and separator gives the original word as its initial segment, followed by $01$ and the remaining dropped suffix. Since the initial-run length is even, it is $2\lfloor tRun(y)/2\rfloor$. Replacing that initial segment by the corresponding doubled unary word and using `pairEncode_eq_dbl` yields the required encoding with canonical suffix.

**Key facts.** `Complexity.LogProg.dbl_replicate`, `Complexity.LogProg.getElem?_lt_tRun`, `Complexity.LogProg.tRun_le`, `Turing.pairEncode_eq_dbl`.
