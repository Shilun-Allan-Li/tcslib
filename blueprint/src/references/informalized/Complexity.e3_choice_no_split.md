<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_choice_no_split -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No verifier membership without a valid split

**Claim.** If the bounded search finds no integer $n$ satisfying $n+C\cdot2^{(n+1)^c}=|y|$, then $y$ does not belong to the choice-word verifier language for $N,C,c$.

**Proof.** Suppose, to the contrary, that verifier membership supplies strings $x,u$ with $y=xu$ and $|u|=C\cdot2^{(|x|+1)^c}$. Taking lengths in the concatenation gives $|y|=|x|+C\cdot2^{(|x|+1)^c}$, so $n=|x|$ is a solution to the equation that the bounded search checks. The characterization of search failure says that returning no value is equivalent to there being no such natural number (\texttt{Complexity.e3_split_none_iff}), a contradiction.

**Key facts.** `Complexity.e3_split_none_iff`.
