<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satClean_install -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time clean installation

**Claim.** Every polynomial-time computable Boolean-word function has a finite machine with at least one work tape that first halts within a polynomial time bound, installs the result on its first work tape with the other tapes blank and canonical heads and input position, and has empty output.

**Proof.** Choose a machine $F$ and constants $A,d$ witnessing polynomial-time computability of $f$. The install-call construction (Turing.FinTM.exists_installCallTM) gives a machine $C$ with designated entry and exit states and at least one work tape. From the prescribed initial arrangement, $C$ reaches its exit with $f(z)$ installed on the first work tape, all other work tapes blank, and empty output. Its time is bounded by $c(T(|z|)+|z|+|f(z)|+1)$, with $T(m)=A(m+1)^d$. The output-length bound Turing.MultiTapeTM.output_length_le, applied using Turing.FinTM.computesInTime_iff, gives $|f(z)|\le T(|z|)$. Replace the output-length term by this bound, then apply the stopping-wrapper result (Complexity.satClean_stop) to make the wrapper halt silently at the exit, adding one step. The polynomial bridge estimate (Complexity.sat_bridge_bound) bounds the resulting time by $(c(2A+1)+1)(|z|+1)^{d+1}$. The wrapper keeps the installed tape contents and canonical head positions, and its output remains empty, as required.

**Key facts.** `Turing.FinTM.exists_installCallTM`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Complexity.satClean_stop`, `Complexity.sat_bridge_bound`.
