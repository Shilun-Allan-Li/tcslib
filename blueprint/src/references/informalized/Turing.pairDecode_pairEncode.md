<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.pairDecode_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair parser inverts pair encoding

**Claim.** For any finite Boolean strings $x$ and $\alpha$, parsing their pair encoding succeeds and returns exactly $(x,\alpha)$.

**Proof.** Induct on $x$. When $x$ is empty, its encoding begins with the delimiter $01$, so the parser returns the empty first component and the remaining string $\alpha$. For the inductive step, write $x=b::x'$. Its encoding begins with the doubled pair $bb$, followed by the encoding of $x'$ and the delimiter and tail. The parser consumes $bb$ and recursively parses the remainder. By induction that recursive result is $(x',\alpha)$; restoring the consumed bit gives $(b::x',\alpha)$, as claimed.
