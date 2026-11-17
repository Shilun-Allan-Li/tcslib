<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/Relativization.lean :: Complexity.exists_entry -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First Entry into the Stage Sets

**Claim.** Every word in the union of the positive stage sets belongs to some stage set $P_{s+1}$ but not to the preceding set $P_s$.

**Proof.** Since $z$ belongs to the union, there is at least one stage index at which it belongs. Choose the least such index $j$ (`Nat.find`). This index is positive, because the zeroth stage has empty positive set. Set $s=j-1$. By the defining property of the least index, $z$ belongs to $P_j$ and does not belong to any earlier stage, in particular not to $P_{j-1}$. Since $j-1+1=j$, these are exactly the desired membership and nonmembership statements.
