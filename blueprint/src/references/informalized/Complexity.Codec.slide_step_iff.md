<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Step.lean :: Complexity.Codec.slide_step_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Local Characterization of a Machine Step

**Claim.** The padded local update condition is equivalent to requiring that every output cell is the corresponding cell of the updated configuration and that this configuration remains within the radius-$s$ window.

**Proof.** Index the encoded cells of $C$ by $0,\ldots,2s$, with two empty cells prepended. At a position $j+1$ in the sliding check, the three input cells are the left neighbor, cell $j$, and the right neighbor; at the two ends, the missing neighbors are the prescribed empty cells. The output at this position is the $j$th entry of $v$. The cell update identity `cellOf_apply` says that applying the local rule to these three cells produces exactly the encoded cell of $a.apply C$ at $j$. Consequently, the checks at positions $1$ through $2s+1$ are equivalent to equality of every entry of $v$ with that updated cell.

There are also two endpoint checks. At position $0$, the output is the empty boundary cell and the local rule sees the left boundary configuration; at position $2s+2$, it sees the right boundary configuration and the output is again empty. Together these say that updating the two boundary cells leaves them empty. The boundary criterion `boundary_iff` identifies exactly these two conditions with the updated configuration having all work-tape heads and nonblank contents within radius $s$. Hence the full set of sliding checks is equivalent to the cell equalities and the window condition.

**Key facts.** `Complexity.Codec.boundary_iff`, `Complexity.Codec.cellOf_apply`.
