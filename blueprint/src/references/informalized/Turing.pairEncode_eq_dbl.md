<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairEncode_eq_dbl -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Encoding via Doubling

**Claim.** For any two bit strings $x$ and $y$, encoding the pair $(x,y)$ gives the concatenation of the string obtained by writing each bit of $x$ twice, the separator $01$, and $y$.

**Proof.** Both sides are given by the same list expression: the encoding starts with the list formed by replacing each bit $b$ of $x$ by $[b,b]$, then appends $[0,1]$ and $y$. The definition of doubling is precisely this replacement-and-concatenation operation, so the equality holds by unfolding the definitions.
