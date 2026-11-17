<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.of_blockSafe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Safe Straight-Line Block

**Claim.** A block-safe statement whose block cost is at most $T$ executes within cost $T$ and ends at its prescribed transformed state, so any predicate true of that state holds at the execution endpoint.

**Proof.** Proceed by cases on the statement. For `skip`, its prescribed state is unchanged and its execution has zero cost (`Light.Ends.skip`). For an assignment, block safety gives expression safety, and the block-cost bound gives the assignment's cost bound; the assignment execution principle (`Light.Ends.set`) reaches exactly the prescribed updated state. For a store, the three parts of block safety supply safety of the address and value and validity of the address; the store execution principle (`Light.Ends.store`) then reaches the prescribed memory update within its block cost.

For a sequence, first execute the first component by induction using its block cost, then execute the second from the resulting prescribed state using its block safety there. The sequential composition principle (`Light.Ends.seq`) combines these executions, and the sequence's block cost is the sum of the two costs. For a conditional, use the conditional execution principle (`Light.Ends.ite`) with branch budget the maximum of the two branch block costs. Whichever branch is selected is block-safe and has cost at most that maximum; its prescribed endpoint is the conditional's prescribed transformed state. The bound follows from the condition cost plus one and that maximum being at most the conditional block cost. A while loop or call cannot arise: by definition, block safety for either form is false, so its assumed proof is eliminated.

**Key facts.** `Light.Ends.skip`, `Light.Ends.set`, `Light.Ends.store`, `Light.Ends.seq`, `Light.Ends.ite`.
