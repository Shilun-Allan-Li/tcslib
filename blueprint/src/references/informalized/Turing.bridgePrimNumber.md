<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgePrimNumber -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursiveness of the Sentinel Code

**Claim.** The function sending a finite Boolean string to the result of folding the binary bit-append operation from initial value $1$ is primitive recursive.

**Proof.** Use primitive recursion over the list. The initial value is the constant $1$. At each list element, the next value is obtained by applying the primitive-recursive binary operation $\operatorname{Nat.bit}$ to the Boolean element and the accumulated code. The Boolean element and accumulator are projections from the recursion's input pair, so composing those projections with the primitive-recursive bit operation gives a primitive-recursive step function. The primitive-recursive list-fold operation therefore yields the sentinel-code function.

**Key facts.** `Turing.codePrimBit`.
