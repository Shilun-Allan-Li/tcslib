<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bin.lean :: Complexity.LogProg.bitsVal_lt_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Word Value Bound

**Claim.** For every finite bit string $w$, its value is strictly less than $2^{|w|}$.

**Proof.** Induct on the word. The empty word has value $0<1$. For a word $b::w$, its value is $b+2\,\mathrm{bitsVal}(w)$, where $b$ is either $0$ or $1$. By induction, $\mathrm{bitsVal}(w)<2^{|w|}$, so the value is at most $1+2(2^{|w|}-1)<2^{|w|+1}$. This is the required bound because $|b::w|=|w|+1$.
