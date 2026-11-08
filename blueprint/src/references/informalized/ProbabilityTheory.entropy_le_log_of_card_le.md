<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Entropy/Basic.lean :: ProbabilityTheory.entropy_le_log_of_card_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entropy bounded by logarithmic alphabet size

**Claim.** If $X$ takes values in a finite nonempty set $S$ with $|S|\le N$, then $H[X;\mu]\le \log N$.

**Proof.** The entropy of a random variable valued in a finite set is at most the logarithm of the size of that set: $H[X;\mu]\le\log |S|$ (\texttt{entropy\_le\_log\_card}). Since $S$ is nonempty, $|S|>0$, and the assumed cardinality bound gives $|S|\le N$. Monotonicity of the logarithm on positive reals therefore yields $\log |S|\le\log N$. Combining the inequalities proves the result.

**Caveat.** The supplied informal statement describes a different claim; this account follows the formal statement and proof source, which establish the logarithmic alphabet-size bound.
