<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satClean_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-time clean emission

**Claim.** Every polynomial-time computable Boolean-word function has a finite machine with at least one work tape that first halts within a polynomial time bound, leaves the result on its first work tape with all other tapes blank and the canonical heads and input position, and emits exactly that result.

**Proof.** Choose a machine $F$ and constants $A,d$ witnessing polynomial-time computability of $f$. The call-machine construction (Turing.FinTM.exists_emitCallTM) gives a machine $C$ with an entry and exit state and at least one work tape. On input $x$ with argument $z$ arranged on its first work tape, $C$ reaches its exit state with $f(z)$ on that tape, the other work tapes blank, and output $f(z)$. Its running time is bounded by $c(T(|z|)+|z|+|f(z)|+1)$, where $T(m)=A(m+1)^d$. The output-length bound for a machine running for $T(|z|)$ steps, namely $|f(z)|\le T(|z|)$, follows from Turing.MultiTapeTM.output_length_le together with the time-computation characterization Turing.FinTM.computesInTime_iff. Substituting this estimate into the call bound gives the polynomial bound used for the bridge. Apply the stopping-wrapper result (Complexity.satClean_stop) to turn reaching the exit state into a first halt, adding one step to the budget. Finally, Complexity.sat_bridge_bound bounds this enlarged running time by $(c(2A+1)+1)(|z|+1)^{d+1}$. The wrapper preserves the specified tape contents and heads, and its halt is silent, so it meets the clean-emission contract.

**Key facts.** `Turing.FinTM.exists_emitCallTM`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Complexity.satClean_stop`, `Complexity.sat_bridge_bound`.
