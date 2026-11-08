<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/MathlibBridge.lean :: Turing.bridgeStack_read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading the Top of a Represented Stack

**Claim.** For every finite stack word $xs$ over the compiled stack-machine alphabet, the tape representation at position $-|xs|$ is the first symbol of $xs$, embedded in the bridge alphabet; if $xs$ is empty, this value is blank.

**Proof.** At the position $z=-|xs|$, adding the stack length gives zero, so the representation’s index condition holds and the list index is zero. Thus the tape value is the optional first entry of $xs$, mapped into the bridge alphabet. If the list is empty, this optional entry is absent, which is precisely the blank value.
