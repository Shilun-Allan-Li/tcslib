<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/LogspaceUniformScan.lean :: BoolCircuit.AdjScan.astep_rd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-step oracle read

**Claim.** If the oracle on encoded natural numbers returns the corresponding bit of $E$, defaulting to false beyond its end, then a read instruction at $l$ with successors $l_1,l_0$ preserves $(p,c,a)$ and branches to $l_1$ exactly when the $p$th bit of $E$, defaulting to false, is true.

**Proof.** A read instruction is an oracle call on the unary prefix of the input together with the bit representation of register $p$. The virtual word supplied to that call is precisely the encoding of the unary prefix and those register bits (`Complexity.LogProg.vword_unary₁`). Thus the oracle hypothesis evaluates the call as $E.getD(p,\mathrm{false})$. The machine’s call transition selects $l_1$ for a true oracle answer and $l_0$ otherwise, and preserves the registers and result.

**Key facts.** `Complexity.LogProg.vword_unary₁`.
