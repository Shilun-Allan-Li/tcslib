<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHost.lean :: Turing.ClockHost.heads_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Idle Tape Heads

**Claim.** For every $n$ and every function $P:\mathrm{Fin}(n)\to\mathbb Z$, adding the movement specified by the idle action leaves $P$ unchanged.

**Proof.** The idle action has movement zero. Hence at each index $i$, the resulting value is $P(i)+0=P(i)$. Since the two functions agree at every index, they are equal.
