<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/UniversalStartup.lean :: Turing.universalPrefix_live -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Prefix Parser Liveness

**Claim.** For every $s<2|\alpha|+2$, the prefix parser has not halted after $s$ steps on the encoded input.

**Proof.** The penultimate-time result identifies the configuration after $2|\alpha|+1$ steps: it is still live, with its parser state recording the separator bit $0$ (`universalPrefix_penultimate`). Since $s<2|\alpha|+2$, we have $s\le 2|\alpha|+1$. A machine that is live at time $t$ must also have been live at every earlier time (`universal_live_before`), so the configuration at time $s$ is live as claimed.

**Key facts.** `Turing.universal_live_before`, `Turing.universalPrefix_penultimate`.
