<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/UHaltMachine.lean :: Complexity.primrec_replicate_numOfString -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Primitive Recursion of the Replicated Encoding

**Claim.** For each Boolean word $s$, the list consisting of $m(s)$ copies of true depends primitively recursively on $s$.

**Proof.** First, the one-step operation on a bit $b$ and current value $v$ is primitive recursive: it returns $2v$ when $b=0$ and $2v+1$ when $b=1$. This is exactly the bit operation $2v+b$. Iterating this operation by primitive recursion over the reversed word, starting from the constant value $1$, shows that $m(s)$ is primitive recursive. Separately, the map sending a natural number $n$ to a list of $n$ copies of true is primitive recursive: form the list of the first $n$ natural numbers and map the constant true value across it. Composing this map with $m$ proves the claim.
