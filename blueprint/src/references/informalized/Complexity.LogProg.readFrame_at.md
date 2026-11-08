<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.readFrame_at -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Read configuration frame

**Claim.** The configuration formed by entering state $l$, setting input-head position $ip$, and placing the binary representation of $k$ on tape $s$ with its head at $0$ lies in the read frame of $c$, with the required bounds on the heads at $s$ and $r$.

**Proof.** The read configuration is itself the special case of the register-updated read configuration in which the state remains $l$, tape $s$ retains the binary tape content, and its head position is $0$. The frame-preservation result for register updates (`Complexity.LogProg.readFrame_reg`) applies with these choices. Its bounds hold: tape $s$'s head is at $0$, and tape $r$'s head remains at its original position $0$, because the indices are distinct and the original head on $r$ is at $0$. Both positions lie in the required interval.

**Key facts.** `Complexity.LogProg.readFrame_reg`.
