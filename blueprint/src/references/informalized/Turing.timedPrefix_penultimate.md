<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Universal.lean :: Turing.timedPrefix_penultimate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Parser Remains Active

**Claim.** For any three finite bit strings $b,\alpha,x$, the prefix parser on $\langle\langle b,\alpha\rangle,x\rangle$ is in a nonhalting state after $4|b|+2|\alpha|+5$ steps.

**Proof.** First establish the parser's configuration at time $4|b|+4+2|\alpha|$: it is in the first code-reading phase, with the input head positioned to read the first bit of the encoded pair $(\alpha,x)$, the clock containing $b$, and the output containing $\alpha$ (`Turing.timedPrefix_code`). The next input bit is the separator bit $\mathsf{false}$, as follows from the pair encoding and the indexed-input identity (`Turing.timed_code_get`, `Turing.timed_pair_separator`). On this bit, the transition from the first code-reading phase enters the second code-reading phase carrying $\mathsf{false}$, emits nothing, and advances the head by one position (`Turing.timedPrefix_advance`). Thus after one more step, at time $4|b|+2|\alpha|+5$, the state is that second phase, which is nonhalting.

**Key facts.** `Turing.timedPrefix_code`, `Turing.timed_code_get`, `Turing.timed_pair_separator`, `Turing.timedPrefix_advance`.
