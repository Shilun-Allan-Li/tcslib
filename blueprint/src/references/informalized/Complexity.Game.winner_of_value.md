<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/Games.lean :: Complexity.Game.winner_of_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Value Determines the Winner

**Claim.** Under the stated greedy-strategy hypotheses, if the position value at history $h$ with $r$ moves remaining is $b$, then the outcome after those moves is $b$.

**Proof.** Proceed by induction on the number $r$ of remaining moves, allowing the current history to vary. If $r=0$, the outcome is $W(h)$, which equals the position value and hence $b$. For the induction step, write $r=r'+1$. The length condition gives $n-(|h|+1)=r'$, so the first player's greedy choice at $h$ evaluates the position after appending true with exactly $r'$ moves left. If $h$ has even length, the first player moves: when the current value is true, the disjunction defining that value ensures that the true-successor or false-successor value is true, and the greedy first player chooses true precisely when its successor value is true. Thus the chosen successor has value true. If the current value is false, the disjunction forces both successor values false, so whichever move is made leads to a false-valued successor. If $h$ has odd length, the second player moves and the value is the conjunction of the successor values. When it is true, both successors have value true, so either move preserves true. When it is false, at least one successor has value false; the second player's negated greedy choice selects a false-valued successor. In every case the next history has length increased by one, the remaining count is $r'$, and its position value is $b$. Apply the induction hypothesis there to conclude that the final outcome is $b$.
