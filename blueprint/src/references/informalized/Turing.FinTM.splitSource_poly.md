<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitSource_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Unary Output

**Claim.** For every $c,C$ and Boolean word $s$, the polynomial unary generator started at loop level $c$ on the prepared bank halts after $T_{c+1}(|s|+1)+1$ steps with unchanged bank tapes and output of $C(|s|+1)^{c+1}$ ones.

**Proof.** Set $q=|s|+1$, which is positive. The generator's loop-end result (`splitPoly_loop_end`) states that from the loop state at level $c$, after `catalogPolyCost $q$ $C$ $(c+1)+1` steps, the machine is in the terminal advance configuration with output consisting of $Cq^{c+1}$ ones and with the same unary bank and head positions. Rewriting the prepared bank as the generator's standard configuration at parameter $q$, and unfolding the cost recurrence, identifies this step count with $T_{c+1}(q)+1$. The terminal configuration is precisely the claimed halted bank configuration.

**Key facts.** `Turing.FinTM.splitPoly_loop_end`.
