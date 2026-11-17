<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_first_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the First Component

**Claim.** For bit strings $a,b$ and $i<|a|$, the bit at position $2i$ in their self-delimiting pairing is the bit of $a$ at position $i$.

**Proof.** The pairing read formula says that a position strictly before $2|a|$ reads from the first component at half that position (`Complexity.pairEncode_getD`). Since $i<|a|$, we have $2i<2|a|$, and the integer quotient $(2i)/2$ is $i$. Substituting these facts gives the claimed equality, including the default value used for out-of-range reads.

**Key facts.** `Complexity.pairEncode_getD`.
