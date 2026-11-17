<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/Odometer.lean :: Light.length_digitsLE -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Digit-list length

**Claim.** For all natural numbers $b,n,c$, the list of the first $n$ base-$b$ digits of $c$ has length $n$.

**Proof.** By definition, this is the image of the length-$n$ list $[0,1,\ldots,n-1]$ under the function sending each position $k$ to $\lfloor c/b^k\rfloor\bmod b$. Mapping a function over a list preserves its length, so the resulting list has length $n$.
