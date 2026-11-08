<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Group_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Wired Tableau Group

**Claim.** For any assignment, a wired clause group evaluates to true exactly when the corresponding bit-level template condition holds, with the source block read at time $s$, target block at time $t$, and selected input bit at index $p$.

**Proof.** Let $B$ be the block width and form the template assignment by reading the assignment along the group’s wire map. The first $B$ template coordinates are wired to the source block at time $s$, so their source-bit slice agrees with that block. The next $B$ coordinates are wired to the target block at time $t$, so their target-bit slice agrees with that block. The final coordinate is wired to position $p$, hence supplies the selected input bit. The template-evaluation identity (`Complexity.clTemplate_eval`) says that evaluating the relabeled clause formula is exactly evaluating its Boolean predicate on this wired assignment. Substituting the three slice identities into that predicate gives, in each template kind, the corresponding condition: the initial block equals the prescribed initial configuration, the state and input slices satisfy their transition requirements, the chosen work-tape slice has the prescribed written-or-kept symbol, or the source snapshot meets the acceptance condition. Thus evaluation is true exactly when the stated template meaning holds.

**Key facts.** `Complexity.clTemplate_eval`.
