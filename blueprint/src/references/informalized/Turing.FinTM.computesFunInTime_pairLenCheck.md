<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.computesFunInTime_pairLenCheck -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time pair-length check

**Claim.** For any natural numbers $C$ and $e$, a finite Boolean Turing machine outputs one bit that is true exactly when parsing succeeds with components $(a,b)$ satisfying $|b|\le C(|a|+1)^e$, and false when parsing fails; its running time is bounded by a constant times $(|x|+1)^{e+1}$.

**Proof.** First compute the parsed first component, using the empty word when parsing fails, in linear time (`computesFunInTime_pairFst`). Separately, a unary-output machine produces a word of length $C(|y|+1)^e$ on input $y$ in time bounded by a constant times $(|y|+1)^{e+1}$ (`computesFunInTime_polyUnary`). Compose these computations: the resulting word has length $C(|a|+1)^e$ when parsing succeeds, and the first-component length bound ensures the composed computation still has polynomial time of the required degree (`computesFunInTime_comp`, `f2_first_length`). Finally, apply the pair-count machine to compare the parsed second-component length with the length of this unary word; it outputs false on parse failure (`pairCount_computes`). The explicit bounds in the proof combine into a constant times $(|x|+1)^{e+1}$, and increasing the time bound preserves the output (`ComputesInTime.mono`).

**Key facts.** `Turing.FinTM.computesFunInTime_pairFst`, `Turing.FinTM.computesFunInTime_polyUnary`, `Turing.FinTM.computesFunInTime_comp`, `Turing.FinTM.f2_first_length`, `Turing.FinTM.pairCount_computes`, `Turing.FinTM.ComputesInTime.mono`.
