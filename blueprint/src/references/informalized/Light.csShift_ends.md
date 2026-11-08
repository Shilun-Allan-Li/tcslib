<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.csShift_ends -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting-sort shift phase

**Claim.** Starting after all items have been placed, the shifting program terminates within cost $18N+9$, leaving each item at its stable sorted position, each counter cell equal to the cumulative count of keys below its index, and memory unchanged outside the destination and counter ranges.

**Proof.** Unpack the initial state, whose memory agrees with the original memory outside the destination and counter ranges and satisfies the placement invariant. Initialize the loop index to $N$. The shift-loop invariant says that, when the index is $s$, the still-waiting counter value at $s$ is available and the already shifted portion has the required form. The initialization lemma for this invariant (`CsShifted.start`) follows from the completed-placement condition.

In a round with index $s+1$, the program copies the value at counter cell $s$ into cell $s+1$, then decreases the index. By the waiting-value property in the invariant, the copied value is the cumulative count for $s$. The one-step invariant lemma (`CsShifted.succ`) establishes the invariant for index $s$ after this update. Each write is within the counter range, so the memory-agreement condition outside the destination and counter ranges is preserved (`SameOutside2.update`). The loop executes exactly $N$ such rounds, as captured by the while-loop execution bound (`Ends.whileBlock`).

At index zero, the program writes zero to the first counter cell. The terminal invariant lemma (`CsShifted.last`) then gives the required cumulative counts, sorted placements, and agreement of memory outside the two ranges. The final write is a valid bounded-cost store (`Ends.storeTo`); sequencing the initialization, loop, and final store gives the stated total bound (`Ends.next`).

**Key facts.** `Light.CsShifted.start`, `Light.Ends.whileBlock`, `Light.CsShifted.succ`, `Light.SameOutside2.update`, `Light.CsShifted.last`, `Light.Ends.storeTo`, `Light.Ends.next`.
