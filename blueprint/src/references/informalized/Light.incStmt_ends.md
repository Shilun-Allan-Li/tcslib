<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Odometer.lean :: Light.incStmt_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a digit increment

**Claim.** Under the stated space, word, digit, and segment hypotheses, the digit-increment statement executes within cost $14|l|+5$, preserves locations, writes the incremented digits on the segment, and leaves memory unchanged outside it.

**Proof.** Induct on the list $l$, generalizing over the segment offset $j$ and memory. If the list is empty, the statement is a skip: the segment condition is vacuous, locations are unchanged, and memory is unchanged outside the empty segment (`Ends.skip`).

For a nonempty list $x::l$, the segment condition identifies the first memory entry with $x$ and gives the segment condition for the tail starting one address later (`seg_cons`). The hypothesis on digits gives $x<n$. The statement tests whether the current digit plus one is less than $n$, and the address and word hypotheses ensure the test and store are safe. Execution of the conditional is assembled from its two branch executions (`Ends.iteLast`).

If the test holds, the statement stores $x+1$ at the first address. This is exactly the first digit of the incremented list in the no-carry case; the tail remains correct because this store is outside the tail segment (`Seg.update_out`). Since the changed address is inside the full segment, memory still agrees with its original values outside that segment (`SameOutside.refl` and `SameOutside.update`). The final store is bounded as required by `Ends.storeLast`.

If the test fails, the first digit is reset to zero and the statement recursively increments the tail at offset $j+1$. The induction hypothesis supplies the execution and the correct incremented tail. The first store makes the leading digit zero, while the tail's starting address lies outside that store, so its segment property is preserved (`Seg.update_out`). Combining the leading zero with the incremented tail gives the carry case of `incDigits`. For addresses outside the full segment, the leading store and recursive execution both preserve the original memory; the update facts for `SameOutside` and the induction hypothesis give the stated agreement. The store followed by the recursive execution is bounded by `Ends.storeThen`. The branch cost bounds combine to the claimed $14|l|+5$ bound.

**Key facts.** `Light.seg_cons`, `Light.Ends.iteLast`, `Light.Seg.update_out`, `Light.SameOutside.refl`, `Light.SameOutside.update`, `Light.Ends.storeLast`, `Light.Ends.storeThen`.
