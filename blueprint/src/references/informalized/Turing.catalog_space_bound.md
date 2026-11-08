<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.catalog_space_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Visited Tape Cells

**Claim.** If head $i$ always lies between $-1$ and $L$, inclusive, then it visits at most $L+2$ distinct cells from time $0$ through time $t$.

**Proof.** The hypothesis places every head position through time $t$ in the integer interval $[-1,L]$. The visited-cell bound for an interval (`Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`) therefore bounds the number of distinct visited positions by the size of that interval, namely $((L+1)-(-1))$ converted to a natural number. This quantity is $L+2$, giving the result.

**Key facts.** `Turing.MultiTapeTM.spaceUsedByTape_le_card_Icc`.
