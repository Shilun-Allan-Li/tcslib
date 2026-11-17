<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopCall_reframe -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reframing a Body Call

**Claim.** The frame assembled from the original call, but with the second call’s control state, input position, flag, counter, and payload data, is exactly the call formed with the second startup bit and updated parameters.

**Proof.** The two configurations have the same state, input-head position, and output by their definitions. To compare their work tapes and head positions, fix a tape index and split into the three distinguished controller tapes: the flag tape, counter tape, and payload tape. On the flag tape, both configurations store the second flag at the origin and are blank elsewhere, with head at the origin. On the counter tape, both store the buffer of the second counter word and have head at the origin. On the payload tape, the frame stores the buffer of the original output, with head at its length; the call configuration’s payload is likewise the buffer of that output and its head is at that length. Every remaining tape belongs to the body or fuel portion. The frame retains those tapes and heads from the original call, while the second call has the same body tapes from the configuration with only its state replaced, and the same fuel tapes. Thus those components agree as well, proving equality of configurations.
