<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/CountSort.lean :: Light.countSort_meets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting sort execution and output

**Claim.** Under the stated counting-sort preconditions, the counting-sort routine executes within cost $68n+58b+52$, places every item at its stable sorted position, leaves the specified cumulative counts in the counter array, and preserves memory outside the destination and counter intervals.

**Proof.** The standard argument frame, padded with zero entries, represents the supplied arguments; the padding does not change the frame (frame_append_zeros). Starting from this state, apply the execution result for each phase in program order: initialize the counters, count the keys, form prefix sums, place the items, and shift the counters. The phase results establish the successive state invariants: zeroed counters, bucket frequencies, cumulative counts, item placement with updated positions, and finally the required output counts and preservation of memory outside the two work intervals. At each composition, the endpoint invariant from one phase is the starting invariant for the next. The execution-composition theorem (Ends.next) combines these phase executions, and monotonicity of the endpoint specifications (Ends.mono) carries the intermediate invariants forward. The phase cost bounds add to $15b+23+(30n+6)+(25b+6)+(38n+6)+(18b+9)=68n+58b+50$, which is within the stated bound $68n+58b+52$. Since the program entry is the counting-sort body, (Meets.of_body) gives the claimed routine execution.

**Key facts.** `Light.frame_append_zeros`, `Light.csZero_ends`, `Light.csCount_ends`, `Light.csPrefix_ends`, `Light.csPlace_ends`, `Light.csShift_ends`, `Light.Ends.mono`, `Light.Ends.next`, `Light.Meets.of_body`.
