<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTab.lean :: Complexity.Meyer.ctrVal_lt -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Boolean Word Value

**Claim.** For every finite Boolean word $w$, its binary value is strictly less than $2^{|w|}$.

**Proof.** Proceed by induction on $w$. The empty word has value $0$, which is less than $2^0=1$. For a word with head bit $b$ and tail $w$, its value is either $2\,\mathrm{ctrVal}(w)$ or $1+2\,\mathrm{ctrVal}(w)$. By induction, $\mathrm{ctrVal}(w)<2^{|w|}$, so either value is strictly less than $2\cdot 2^{|w|}=2^{|w|+1}$, the required bound for the longer word.
