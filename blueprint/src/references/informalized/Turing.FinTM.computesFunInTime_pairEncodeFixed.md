<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_pairEncodeFixed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair encoding with a fixed first component

**Claim.** For every fixed Boolean word $\alpha$, a finite Boolean Turing machine and a constant compute the pair encoding $(\alpha,x)$ on every Boolean input $x$ within a number of steps linear in $|x|+1$.

**Proof.** Fix $\alpha$ and let $w$ be the word formed by doubling each bit of $\alpha$ and then appending the separator $01$. The fixed-prefix computation theorem gives a machine that outputs $w$ followed by its input $x$ in time bounded by a constant times $|x|+1$ (`computesFunInTime_prepend`). By the definition of pair encoding, this output is precisely the encoding of $(\alpha,x)$.

**Key facts.** `Turing.FinTM.computesFunInTime_prepend`.
