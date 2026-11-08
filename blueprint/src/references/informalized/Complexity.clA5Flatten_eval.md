<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Flatten_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a Flattened CNF

**Claim.** For a list $G$ of CNF formulas and a Boolean assignment $a$, the flattened formula evaluates to true exactly when every formula in $G$ evaluates to true under $a$.

**Proof.** Induct on the list of formulas. The empty list flattens to the empty CNF, which evaluates to true, and the universal condition over its members is vacuous. For a list with head formula $g$ and remaining list $G'$, flattening concatenates $g$ with the flattening of $G'$. CNF evaluation over a concatenation is the conjunction of the evaluations of its parts. Thus the flattened formula is true exactly when $g$ is true and the flattening of $G'$ is true; the induction hypothesis turns the latter condition into truth of every formula in $G'$. Together these are precisely truth of every formula in the original list.
