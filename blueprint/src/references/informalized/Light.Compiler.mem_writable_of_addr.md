<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Compiler/Cells.lean :: Light.Compiler.mem_writable_of_addr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Address Is Writable

**Claim.** Let $Z$ be a compiler size configuration, $q$ a natural number, and $a$ an integer. If $0\le a<Z$'s space limit, then $a$ belongs to the writable address set determined by $Z$ and $q$.

**Proof.** The writable set is a union whose final component consists precisely of addresses $a$ satisfying $0\le a<Z$'s space limit. The hypothesis places $a$ in that component, and therefore in the full union.
