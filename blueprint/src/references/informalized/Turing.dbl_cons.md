<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.dbl_cons -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Doubling a leading bit

**Claim.** For every Boolean bit $b$ and finite Boolean word $w$, doubling the word formed by placing $b$ at the beginning of $w$ gives two copies of $b$ followed by the doubling of $w$.

**Proof.** By definition, doubling replaces each bit by two consecutive copies. Applying this to the first bit $b$ and then to the remaining word $w$ gives $b,b$ followed by the doubled remainder.
