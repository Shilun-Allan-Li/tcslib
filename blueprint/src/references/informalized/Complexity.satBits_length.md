<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satBits_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of a Doubled Word

**Claim.** Replacing every bit of a Boolean word $x$ by two copies produces a word of length $2|x|$.

**Proof.** Induct on $x$. The empty word has doubled length zero. For a word with first bit $b$ and tail $x$, its doubled word consists of the two copies of $b$ followed by the doubled tail. Its length is therefore $2$ plus the length of the doubled tail; by induction this is $2+2|x|=2(|x|+1)$, as claimed.
