<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumValue_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Word Value Bound

**Claim.** For every finite Boolean word $u$, its little-endian binary value is strictly less than $2^{|u|}$.

**Proof.** Induct on the word. The empty word has value $0$, which is less than $2^0=1$. For a word with first bit $b$ and remaining word $u$, the value is twice the value of $u$, plus $1$ if $b$ is true and $0$ otherwise. By induction the value of $u$ is less than $2^{|u|}$; since it is an integer, it is at most $2^{|u|}-1$. Thus the value of the whole word is at most $2(2^{|u|}-1)+1<2^{|u|+1}$, as required.
