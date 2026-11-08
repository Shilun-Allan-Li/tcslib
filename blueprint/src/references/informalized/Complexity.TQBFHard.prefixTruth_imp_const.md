<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFHardSemantics.lean :: Complexity.TQBFHard.prefixTruth_imp_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Implication Through a Quantified Prefix

**Claim.** Truth of the quantified prefix with matrix $K\to P(\tau)$ is equivalent to $K$ implying truth of the same prefix with matrix $P(\tau)$.

**Proof.** Induct on the quantifier list, keeping the assignment and starting index arbitrary. For the empty prefix the two sides reduce to the same implication. For an existential first quantifier, the induction hypothesis reduces the claim to moving the fixed antecedent $K$ across the existential choice: if $K$ holds, a witness for the implication supplies a witness for $P$; if $K$ fails, both implications are vacuous. For a universal first quantifier, apply the induction hypothesis at each Boolean value. If the quantified implications hold and $K$ holds, then $P$ holds for every value; conversely, if $K$ implies universal truth of $P$, each value satisfies the corresponding implication.
