<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationAcceptance_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Formula Bounds

**Claim.** For a finite-state Turing machine $M$ with $k$ work tapes, if $C\ge |Q|+6k+5$, then the acceptance formula has at most $C(s+n+1)$ variables and its binary serialization has length at most $4(C(s+n+1)+3)+1$.

**Proof.** The coefficient hypothesis bounds the number of possible codec bits by $C(s+n+1)$ (`Complexity.codecBit_card_le`). Every literal in the acceptance formula is relabeled by the index of a codec bit, so its wire index is below this same bound. The general variable-count estimate for a relabeled CNF (`Complexity.codecCnf_numVars`) gives the claimed variable bound. The serialization estimate (`Complexity.codecCnf_serialize`) bounds the length by the CNF cost times the variable bound plus three, with a final delimiter. For this acceptance formula, the cost and the resulting expression simplify to $4(C(s+n+1)+3)+1$.

**Key facts.** `Complexity.codecBit_card_le`, `Complexity.codecCnf_numVars`, `Complexity.codecCnf_serialize`.
