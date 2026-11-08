<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSolve_source -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Split Solver

**Claim.** Under the stated exact-output and time-bound hypotheses on the source machine, a finite Turing machine computes the encoded prefix and suffix at the least length satisfying the split equation, or returns the empty word when no such length exists, within a polynomial time bound of degree $e+2$.

**Proof.** Apply the split-solver construction to the body built from $M$ and its start state, using the anchor state and the constant $(C+1+5e)2^e+40$. The body starts at the anchor with an empty candidate: `splitBody_start` identifies its initial configuration with that anchored configuration, so startup takes zero steps and cannot revisit the anchor at any earlier positive time.

Now fix an input $w$ and a candidate $s$ of length at most $|w|+1$. The exact source hypothesis supplies an execution on the prepared unary bank that halts with $C(|s|+1)^e$ output ones and unchanged tapes. The split-body round lemma (`splitBody_round`) converts this source execution into a round of the combined body: it has positive duration, avoids the anchor at all strictly intermediate positive times, and either halts with the encoded prefix and suffix when the candidate length plus the source output length equals $|w|$, or returns to the anchor with the next candidate. Its duration is at most $B(|s|)+5|s|+3|w|+20$. The assumed bound on $B$, together with $|s|\le |w|+1$, lets the envelope estimate (`splitBody_envelope`) bound this duration by $((C+1+5e)2^e+40)(|w|+1)^{e+1}$.

The split-solver construction (`splitSolve_of_body`) uses these bounded rounds to search the candidates in order and returns the first one satisfying the equation; if none does, it returns the empty word. Its resulting running-time bound has degree $e+2$, as claimed.

**Key facts.** `Turing.FinTM.splitBody_start`, `Turing.FinTM.splitBody_round`, `Turing.FinTM.splitBody_envelope`, `Turing.FinTM.splitSolve_of_body`.
