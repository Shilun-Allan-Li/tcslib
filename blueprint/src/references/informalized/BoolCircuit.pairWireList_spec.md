<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/PairEncode.lean :: BoolCircuit.pairWireList_spec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair wire list specification

**Claim.** For every $n$ and bit string $r$, the pair wire list has length $2n+2+|r|$, and evaluating its variable wires under any assignment $v$ gives the self-delimiting pairing of the bit string of values of $v$ with $r$.

**Proof.** Fix an assignment $v$. Mapping a function over a list formed by duplicating each entry is the same as first mapping the function and then duplicating each resulting value; this follows by induction on the list. Apply this observation to the list of variable wires. The two copies of each variable wire then evaluate to two copies of the corresponding bit of `List.ofFn v`; the separator constants and the bits of $r$ evaluate to themselves. This is precisely the definition of the self-delimiting pairing. For the length, take lengths on this evaluation identity for any assignment. The length of the encoding of two bit strings is $2|x|+2+|y|$ (`Turing.length_pairEncode`); since `List.ofFn v` has length $n$, the wire list has length $2n+2+|r|$.

**Key facts.** `Turing.length_pairEncode`.
