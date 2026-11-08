<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_splitSolveWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotone-Time Padded Split Search

**Claim.** Given $f$, a machine computing the binary representation of $f(|s|)$ within a monotone time bound $T_E(|s|)$, there are a finite machine and a constant that compute the specified padded split encoding, or the empty word when no split exists, within $c(n+1)(T_E(n+1)+n+2)$ steps.

**Proof.** Apply the closed construction for monotone-time split search to $f$, the given machine $E$, its monotone bound $T_E$, and the assumed computation of the binary representation of $f(|s|)$. That construction returns a finite machine and constant with precisely the required split output and time bound.

**Key facts.** `Turing.FinTM.emitterP2_closed`.
