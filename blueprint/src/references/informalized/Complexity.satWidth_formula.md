<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satWidth_formula -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Formula Width Fold

**Claim.** Scanning the binary encoding of a CNF formula from state $0$, counter $0$, and flag $g$ ends in state $4$, counter $0$, and flag $g\wedge W(\varphi)$, including for the empty formula.

**Proof.** Induct on the list of clauses, allowing the initial flag to vary. For the empty formula, its serialization is the terminal zero bit; from state $0$ this moves the syntax scanner to state $4$, leaves the counter zero, and preserves the flag. For a formula with first clause $C$, its serialization begins with a one bit, which moves the scanner to state $1$. Scanning the encoding of $C$ then returns it to state $0$ and updates the flag according to whether $C$ has at most three literals, by the clause-fold identity (`Complexity.satWidth_clause`) with counter zero. The remaining formula can now be scanned using the induction hypothesis. Its flag update conjoins the width tests for the remaining clauses, so altogether the final flag is $g\wedge W(\varphi)$; the final state and counter are $4$ and zero.

**Key facts.** `Complexity.satWidth_clause`.
