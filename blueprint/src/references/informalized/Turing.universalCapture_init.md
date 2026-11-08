<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalCapture_init -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initialization of the capture wrapper

**Claim.** The capture wrapper’s initial configuration on $x$ equals the first-phase configuration formed from the underlying machine’s initial configuration on $x$.

**Proof.** Compare the five configuration components. The states, input-head positions, and outputs agree directly: both start in the wrapper’s first phase, at the underlying initial input-head position, with empty output. For each work-tape index, split the wrapper’s tape index into the underlying machine’s left block, the single buffer tape, or the right block. In the left block, both tape contents and head positions are those of the underlying initial configuration. On the buffer tape, the underlying output is empty, so its buffered contents are blank everywhere and its head position is zero, as in the wrapper’s initial configuration. The right block is blank with head position zero on both sides. Thus all components agree.
