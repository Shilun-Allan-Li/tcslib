<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the Cook–Levin Tableau

**Claim.** Under the stated computation hypothesis, satisfiability of the tableau formula yields a word $u$ of length exactly $C(|x|+1)^e$ such that $x$ concatenated with $u$ belongs to $V$.

**Proof.** 1. Choose a satisfying assignment $a$ for the tableau formula. The tableau evaluation characterization (\texttt{clA5Tableau\_eval}) gives the input-prefix constraints, the initial-row constraint, all transition and tape constraints, and the acceptance constraints. Put $m=|x|+C(|x|+1)^e$ and read the first $m$ assignment bits as a word $y$. The read-input property (\texttt{clA5ReadInput\_get}) ensures that each of those bits agrees with the corresponding position of $a; the tableau’s prefix constraints in particular make the first $|x|$ bits equal to $x$.

2. Translate the tableau constraints into statements about the actual run of $M$ on $y$. The initial-row, input-row, and work-tape-row interpretations (\texttt{clA5Initial\_meaning}, \texttt{clA5Input\_meaning}, and \texttt{clA5Work\_meaning}) supply the hypotheses for the run-reconstruction lemma (\texttt{clA5Reconstruct}). It follows that each encoded tableau block through time $T$ is the corresponding actual machine snapshot. Consequently, the tableau’s acceptance constraints imply that at every time $t<T$, the emitted symbol is not false.

3. By the decider-acceptance characterization (\texttt{clA5Decider\_accept}), and the assumed computation guarantee for every input of length $m$, these emissions imply $y\in V$. Finally, the certificate lemma (\texttt{clA5Certificate}) splits the read word as $y=x\mathbin{++}u$, with $|u|=C(|x|+1)^e$. Substituting this equality into $y\in V$ proves the claim.

**Key facts.** `Complexity.clA5Tableau_eval`, `Complexity.clA5ReadInput_get`, `Complexity.clA5Initial_meaning`, `Complexity.clA5Input_meaning`, `Complexity.clA5Work_meaning`, `Complexity.clA5Reconstruct`, `Complexity.clBlockDecode_encode`, `Complexity.clA5Decider_accept`, `Complexity.clA5Certificate`.
