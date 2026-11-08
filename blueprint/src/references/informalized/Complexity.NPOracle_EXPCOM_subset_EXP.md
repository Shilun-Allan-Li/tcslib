<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.NPOracle_EXPCOM_subset_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nondeterministic EXPCOM Oracle Time Lies in EXP

**Claim.** Every language decidable by a nondeterministic oracle machine with oracle EXPCOM in time bounded by a constant multiple of $n^c+1$ for some $c$ belongs to EXP.

**Proof.** Take a language in $\mathrm{NP}^{\mathrm{EXPCOM}}$. Unpack its time bound and machine, then replace its nondeterministic choices by a guessed choice string: the choice-machine construction produces a machine whose output records the chosen computation, and membership is witnessed by a choice string of length $2a(n+1)^k$ for suitable constants $a,k$ (`FinOracleNDTM.exists_choiceTM`, `FinOracleNDTM.mem_iff_exists_choiceOut`).

Next replace each oracle query by an ordinary computation. The EXPCOM decider runs in time at most $A2^{B(m+1)}$ on a query of length $m$ (`expcom_decider`). Its time bound is monotone in $m$, so the plain-simulation theorem applies: it constructs a deterministic machine simulating the choice-machine with the oracle-decider cost included in its running time (`FinOracleTM.exists_plain_simulation_of_monotone`). Since the guessed choices have polynomial length, this gives a polynomial-length certificate and a deterministic verifier whose running time is bounded by the explicit simulation expression in the proof.

The certificate-shell construction turns that verifier into a decider for the language of inputs admitting an accepting choice string. Projection of the shell language removes the appended certificate and identifies the resulting language with the original one (`FinTM.exists_certificateShell`, `FinTM.certificateShell_proj`). The choice-string characterization above verifies this equality. Finally, `expcom_summit_budget` bounds the resulting time by an exponential-polynomial budget, and the general inclusion of exponential-polynomial time bounds in EXP yields the claim (`ExpPoly.mem_EXP`).

**Key facts.** `Turing.FinOracleNDTM.exists_choiceTM`, `Turing.FinOracleNDTM.mem_iff_exists_choiceOut`, `Complexity.expcom_decider`, `Turing.FinOracleTM.exists_plain_simulation_of_monotone`, `Turing.FinTM.exists_certificateShell`, `Turing.FinTM.certificateShell_proj`, `Complexity.expcom_summit_budget`, `Complexity.ExpPoly.mem_EXP`.
