<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Tableau_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of Tableau Constraints

**Claim.** The tableau evaluates to true exactly when its input-bit, initial, state-transition, input, work-tape, and acceptance constraints all hold over the stated ranges.

**Proof.** Unfold the tableau as the flattening of its list of constraint groups. The flattening evaluation property (`clA5Flatten_eval`) says that this formula is true exactly when every group in that list evaluates to true. Each initial, state, and acceptance group evaluates to its corresponding meaning by the group-evaluation lemma (`clA5Group_eval`); the input and work groups remain expressed by their evaluations. The list concatenation, mapping, and range structure then gives the stated index ranges. In the work-group part, the list is indexed by tape numbers below the number of tapes, while the conclusion quantifies over tape indices; converting between these is just the correspondence between a natural number below the tape count and its `Fin` index. Thus the group conditions are precisely the listed conjunction.

**Key facts.** `Complexity.clA5Flatten_eval`, `Complexity.clA5Group_eval`.
