<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Scan.lean :: Complexity.Codec.foldl_slStep_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Folded recurrence check

**Claim.** Folding the three-term update over the first $J$ pairs produces the three indicated entries of the padded $f$ and $g$ lists, and its Boolean flag records exactly whether the recurrence holds at every index below $J$.

**Proof.** Proceed by induction on $J$. For $J=0$, the fold leaves the initial state unchanged; the displayed list lookups return the three initial values, and the empty recurrence condition is true. Suppose the result holds for $J$. The range of length $J+1$ is the range of length $J$ followed by its last index, so the fold first reaches the state described by the induction hypothesis and then applies one more update, using $(f(J),g(J))$. The update shifts the stored entries and conjoins the old flag with the new test that the previous second entry equals $G$ of the previous three entries and $f(J)$. The list lookup identities show that the shifted entries are the claimed lookups for length $J+1$: below the new endpoint, appending the final entries leaves lookups unchanged; at the endpoint the new values are $f(J)$ and $g(J)$; one position beyond the old $f$ list the padded lookup is $e$. Finally, the new conjunction of Boolean tests is equivalent to the recurrence holding at every index below $J+1$: split such an index into one below $J$ or equal to $J$. In the first case the old condition applies, and in the endpoint case the new test is precisely the recurrence at $J$. Conversely, the universal condition below $J+1$ supplies both the old conditions and this endpoint test.
