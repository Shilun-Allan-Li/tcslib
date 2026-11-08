<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Clean_install -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Installation from Polynomial-Time Computation

**Claim.** Every polynomial-time computable function on binary words has a finite Turing machine that, on every input and argument, first halts at a positive time bounded by a polynomial in the argument length, leaves its tapes encoding the function value, and has emitted nothing.

**Proof.** Take a machine $F$ computing $f$ within $A(n+1)^d$. The installation-call construction (`Turing.FinTM.exists_installCallTM`) supplies a machine $C$ whose tapes encode $f(arg)$ at a designated exit state, with empty output, and whose exit is not reached at an earlier positive time. Its time bound also involves $|f(arg)|$; this length is at most the source running time by the output-length bound (`Turing.MultiTapeTM.output_length_le`). Hence the call time is bounded using the expression $c(A(n+1)^d+n+A(n+1)^d+1)$. Apply the release-wrapper lemma (`Complexity.clA5Clean_stop`) to make the computation halt cleanly at its first halt, preserving the installed tape contents and empty output. The polynomial bridge bound (`Complexity.clA5_bridge_bound`) then bounds the resulting time by $(c(2A+1)+1)(n+1)^{d+1}$.

**Key facts.** `Turing.FinTM.exists_installCallTM`, `Turing.MultiTapeTM.output_length_le`, `Complexity.clA5Clean_stop`, `Complexity.clA5_bridge_bound`.
