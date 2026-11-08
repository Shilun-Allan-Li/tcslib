<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.run_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulating a Run Within the Clock

**Claim.** If $j+|u|\le m$, then running the host on the choice word $u$ from the representation of $a$ at yard position $j$ yields the representation of $A$'s run on $u$ from $a$, with yard position $j+|u|$.

**Proof.** Induct on the choice word $u$, allowing the initial configuration $a$ and clock position $j$ to vary. For the empty word, both runs leave their configurations unchanged. For a nonempty word $b::u$, the length bound implies $j<m$, so the one-step simulation theorem `run_step` applies to the first choice $b$: it advances the host to the representation of $A$ after its corresponding step and increases the yard position by one. The induction hypothesis then simulates the remaining word $u$ from that updated configuration and position. The bound needed for this application follows from $j+1+|u|\le m$. The resulting clock position is $j+1+|u|$, which equals $j+|b::u|$, proving the claim.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.ClockHost.run_step`.
