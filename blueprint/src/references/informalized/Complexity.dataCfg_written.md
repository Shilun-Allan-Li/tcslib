<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/Oblivious.lean :: Complexity.dataCfg_written -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Origin writes decode correctly

**Claim.** After the totalized source action's writes are encoded at coordinate $0$, the decoded current payload at every lane and coordinate is the source written payload before any head movement.

**Proof.** Fix a lane and coordinate, and split the lane into a work-tape lane or the input lane. On a work-tape lane, first consider coordinate $0$. If the source action has no write there, the tape is unchanged, and the assumed encoding identifies its decoded payload with the old source payload. If it does write, the simulator stores that symbol in a data cell at the origin with blank cached neighbor; decoding the cell returns precisely the written symbol. At a nonzero coordinate, the origin write does not alter the tape, and the function-update rule leaves that coordinate unchanged, so the original encoding hypothesis gives the required source written payload. On the input lane, the simulator prescribes no write, and the source written payload on that lane is the original input payload at every coordinate; hence the encoding hypothesis applies directly.
