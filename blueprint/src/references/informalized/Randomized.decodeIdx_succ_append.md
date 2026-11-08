<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalk.lean :: Randomized.decodeIdx_succ_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a Block and Suffix

**Claim.** Decoding $k+1$ blocks from the concatenation of a Boolean string $u$ of length $b$ with a suffix $l$ returns first $e(u)$ and then the result of decoding $k$ blocks from $l$.

**Proof.** The first decoded block reads the first $b$ entries of the concatenation, using false as a default beyond its end. Since $u$ has length $b$, these entries are exactly the entries of $u$, so the associated Boolean function on indices is $u$ itself and applying $e$ gives $e(u)$. Dropping the first $b$ entries of the concatenation removes precisely the representation of $u$ and leaves $l$. The recursive remainder is thus the decoding of $k$ blocks from $l$, giving the claimed list.
