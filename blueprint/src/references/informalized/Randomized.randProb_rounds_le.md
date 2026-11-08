<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ZPPHosts.lean :: Randomized.randProb_rounds_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Repeated-round halting bound

**Claim.** If every length-$R$ round from a ready configuration either halts or returns to readiness, and the probability of halting in one round is at most $a$, then from any ready configuration the probability of halting after $Rj$ choices is at most $a^j$.

**Proof.** Proceed by induction on $j$, keeping the starting configuration arbitrary. For $j=0$, the probability is at most $1=a^0$. For the induction step, split a random word of length $R+Rj$ into its first round $p$ and its remaining word $v$. The run on the concatenation is the run on $v$ starting from the configuration reached after $p$ (the run concatenation law, `Turing.NDTM.runWith_append`). If that first round has already halted, the remaining choices cannot change the halted configuration (`Turing.NDTM.runWith_of_halt`), so the event of halting on the whole word implies that the first round halted or that the first round returned to a ready configuration and the remainder halts. The round-stability assumption rules out any other outcome. The bound for probabilities of such sequential events (`Randomized.randProb_append_le`) therefore bounds the total probability by the first-round halting probability times the worst-case probability for the remaining $j$ rounds. The first factor is at most $a$ by hypothesis, and the second at most $a^j$ by induction, giving $a^{j+1}$.

**Key facts.** `Randomized.randProb_le_one`, `Turing.NDTM.runWith_append`, `Turing.NDTM.runWith_of_halt`, `Randomized.randProb_append_le`.
