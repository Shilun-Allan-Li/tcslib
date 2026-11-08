<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CfgRecord.lean :: Turing.recordStep_complement_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value of Complementary Binary Words

**Claim.** For every finite Boolean word $u$, the base-$2$ values of $u$ and its bitwise complement sum to $2^{|u|}-1$.

**Proof.** Induct on the word. For the empty word, both digit values are zero and the claimed right-hand side is also zero. For a word with first bit $b$ and tail $u$, the first digits of the word and its complement are opposite, so their contributions to the sum are $b+ (1-b)=1$. The remaining digits contribute twice the value of the tail's length-$|u|$ all-ones total, which by induction is $2(2^{|u|}-1)$. Including the leading place value $2^{|u|}$ in the digit recurrence gives $1+2(2^{|u|}-1)+1$ in the corresponding recurrence arrangement, simplifying to $2^{|u|+1}-1$; equivalently, in either case for $b$, the two recursive expressions sum to $2^{|u|+1}-1$. The elementary bound $1\le 2^{|u|}$ justifies the natural-number subtraction in this simplification.
