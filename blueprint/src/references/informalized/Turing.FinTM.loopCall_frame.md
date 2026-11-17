<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.loopCall_frame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Body Call as a Controller Frame

**Claim.** The body call is exactly the controller frame specified by its resulting control state and the starting input-head position, with the flag, counter, and payload tapes and heads, and output as described.

**Proof.** Use the re-framing identity `loopCall_reframe` with the startup, release, flag, word, and body configuration unchanged, and take the body state parameter to be the state of the call itself. This identity expresses the frame formed from the call as equal to the call. Reversing that equality yields the claimed description: its state is the call's state, its input-head position is $c$'s, the flag tape stores the optional flag at zero and is blank elsewhere, the counter and payload tapes hold the buffered word and output, their heads are at zero and $|c.output|$, respectively, and the output is empty.

**Key facts.** `Turing.FinTM.loopCall_reframe`.
