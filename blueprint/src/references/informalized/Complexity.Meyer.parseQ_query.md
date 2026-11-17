<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.parseQ_query -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parsing an Encoded Query

**Claim.** For any natural number $n$, bit vector $b$, and Boolean words $t,a,x$, parsing their encoded query with bit-vector length $n$ returns exactly $(b,t,a,x)$.

**Proof.** The encoded query begins with the $n$ bits of $b$, so dropping its first $n$ entries leaves the concatenation of the delimiter encoding of $t$, two false bits, the delimiter encoding of $a$, two false bits, and $x$. The query's length formula (`length_query`) shows that the word is long enough for the parser to consume that prefix. The delimiter-reading identity (`readField_fcode`) then parses the first encoded field as $t$ and leaves exactly the material encoding $a$ and $x$; a second application parses $a$ and leaves $x$. The parser's returned bit vector agrees with $b$, since each of its first $n$ entries is the corresponding entry of the query's initial bit prefix. These components together give the claimed result.

**Key facts.** `Complexity.Meyer.length_query`, `Complexity.Meyer.readField_fcode`.
