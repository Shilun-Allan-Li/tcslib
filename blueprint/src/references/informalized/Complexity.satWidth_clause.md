<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satWidth_clause -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause Width Fold

**Claim.** Starting in state $1$ with counter $c$ and flag $g$, scanning the binary encoding of a clause $C$ ends in state $0$, counter $0$, and flag $g\wedge[c+|C|\le 3]$.

**Proof.** Induct on the list of literal occurrences in $C$, allowing the starting counter and flag to vary. For the empty clause, the encoding consists only of its closing separator: it returns the scanner to state $0$ and resets the counter, while the flag is unchanged. Since $c$ is a counter in $\{0,1,2,3\}$, the condition $c+0\le3$ holds. For a clause beginning with literal $\ell$, first scan its literal encoding. The one-literal update (`Complexity.satWidth_literal`) leaves the scanner in state $1$, replaces the counter by its capped increment, and conjoins the flag with $[c<3]$. Apply the induction hypothesis to the remaining clause, then combine the two flag conditions: $c<3$ together with the remaining length fitting within the capped counter is equivalent to $c+|C|\le3$. The closing separator gives the stated final state and zero counter.

**Key facts.** `Complexity.satWidth_literal`.
