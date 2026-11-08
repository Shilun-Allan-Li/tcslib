<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/VWord.lean :: Complexity.lt_of_drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Strict List Drop Bound

**Claim.** If dropping the first $p$ entries of a Boolean list $x$ leaves a nonempty list $b::r$, then $p<|x|$.

**Proof.** Suppose instead that $x$ has length at most $p$. Dropping at least the entire length of a list gives the empty list. This contradicts the hypothesis that the result is $b::r$, which is nonempty. Hence $p<|x|$.
