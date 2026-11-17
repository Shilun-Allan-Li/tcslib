<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHosts.lean :: Randomized.clockHost_zDecides -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clocked Zero-Error Decision

**Claim.** Under the stated hypotheses, the looping clocked host always outputs the correct one-bit membership indicator whenever it halts, and its cumulative nonhalting probability is at most $T_S(n)+m(n)+2+16(m(n)+1)$.

**Proof.** Fix $x$ and write $m=m(|x|)$. The startup lemma (`Turing.ClockHost.startup`) places the host in a ready simulation configuration within $T_S(|x|)+m+2$ steps. Divide subsequent witness bits into rounds of length $R=4(m+1)$. The round lemma (`Turing.ClockHost.round`) says that a successful attempt within a round makes the host halt with that attempt's output, while an unsuccessful attempt returns it to a ready configuration. By the correctness hypothesis and the attempt characterization (`Randomized.attemptBit_eq_some`), every such halted output is the membership indicator.

For any ready configuration, nonhalting after one round implies that the attempt did not produce a bit. The probability of this event is at most $3/4$: monotonicity of random probability (`Randomized.randProb_mono`) bounds it by the probability of an unsuccessful length-$m$ attempt, and truncating the round's bits preserves that distribution (`Randomized.randProb_take`). Iterating over rounds gives a bound $(3/4)^j$ on surviving $j$ rounds (`Randomized.randProb_rounds_le`). The expected-time estimate for round-based processes (`Turing.FinNDTM.expTimeLe_of_rounds`) then bounds cumulative nonhalting probability by the startup cost plus $R/(1-3/4)=16(m+1)$, as claimed.

To show correctness for any witness on which the host halts, pad that witness with irrelevant bits to the end of a whole number of rounds. The halted-rounds principle (`Randomized.halted_rounds`) propagates the round-by-round alternative—either halt with the correct indicator or return ready—until the known halted endpoint, forcing the output to be the indicator. Padding preserves the halted run (`Turing.NDTM.runWith_of_halt`), so the original witness has that same output.

**Key facts.** `Turing.ClockHost.startup`, `Turing.ClockHost.round`, `Randomized.attemptBit_eq_some`, `Randomized.randProb_mono`, `Randomized.randProb_take`, `Randomized.randProb_rounds_le`, `Turing.FinNDTM.expTimeLe_of_rounds`, `Randomized.halted_rounds`, `Turing.NDTM.runWith_of_halt`.
