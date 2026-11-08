<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Formulas/QBF.lean :: Complexity.QBF.satisfiable_of_exPrefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Satisfiability from Existential Quantifiers

**Claim.** If a prefix of $j$ existential quantifiers starting at index $i$ makes $m$ true under $[?]$, then $m$ is satisfiable.

**Proof.** Proceed by induction on $j$, allowing the assignment and starting index to vary. For $j=0$, the prefix has no quantifiers, so its truth says directly that the current assignment makes $m$ evaluate to true; that assignment witnesses satisfiability. For the successor case, truth of the existential prefix supplies a Boolean value $b$ at index $i$ such that the remaining $j$ quantifiers are true under the updated assignment and starting index $i+1$. The induction hypothesis applied to that assignment yields a satisfying assignment for $m$.

**Caveat.** The claim accidentally includes an unrendered placeholder in its assignment phrase; the intended assignment is the given $\sigma$.
