<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Word.lean :: Complexity.Codec.bitsVal_lt_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Value Bound by Word Length

**Claim.** For every finite Boolean list $w$, its binary value is strictly less than $2^{|w|}$, where $|w|$ is the length of the list.

**Proof.** Induct on the list. The empty list has value zero, which is strictly less than $1$. For a list with first bit $b$ and tail $w$, its value is $b$'s value plus twice the tail's value. The bit contributes either zero or one, and by induction the tail value is less than $2^{|w|}$. Thus the whole value is less than $1+2\cdot 2^{|w|}=2^{|w|+1}$, as required.
