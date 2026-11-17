<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.truthAux_exSuffix_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Existential Completion of a Variable Prefix

**Claim.** When $m$ has at most $i+j$ variables, truth under $j$ successive existential choices from index $i$ is equivalent to the existence of a satisfying assignment agreeing with the initial assignment below $i$.

**Proof.** For the forward implication, induct on $j$, allowing the initial assignment and index to vary. If $j=0$, the formula is already true under the initial assignment, which itself agrees with that assignment below $i$. For the successor case, the first existential choice updates the value at $i$; apply the induction hypothesis to the remaining choices, starting at $i+1$, to obtain a satisfying assignment agreeing below $i+1$. In particular it agrees with the original assignment below $i$, since those indices are different from $i$. For the reverse implication, take a satisfying assignment that agrees with the initial assignment below $i$. The fact that existential choices can realize any such satisfying assignment, provided all variables of $m$ lie below $i+j$, gives truth of the prefix (exPrefix_of_satisfying).

**Key facts.** `Complexity.QBF.exPrefix_of_satisfying`.
