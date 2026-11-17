<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPLInP.lean :: Randomized.BPLInP.entryW_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoded transition-entry value

**Claim.** The encoded entry for codes $a$ and $a'$ is the binary representation of the sum of two contributions, one for each fixed choice bit, each equal to $v$ when its transition relation holds and zero otherwise.

**Proof.** On the specified paired input, the pairing projections recover the input $x$, the space parameter $s$, the source code $a$, the target code $a'$, and the value $v$ (`pairFstD_pairEncode`, `pairSndD_pairEncode`). Thus each step test is precisely the indicator of the corresponding fixed-choice transition relation. The entry construction adds the binary representation of $v$ for each test that succeeds and the representation of zero for each test that fails. Since the binary-value map sends the representation of $n$ back to $n$ (`bitsVal_bits`), the arithmetic addition computes the stated natural-number sum; converting that sum back to binary gives exactly the claimed encoding.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.LogProg.bitsVal_bits`.
