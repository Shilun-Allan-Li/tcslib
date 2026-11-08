<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Clean_emit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clean Emission from Polynomial-Time Computation

**Claim.** Every polynomial-time computable function on binary words has a finite Turing machine that, on every input and argument, first halts at a positive time bounded by a polynomial in the argument length, leaves the argument encoded on its tapes, and emits exactly the function value.

**Proof.** Choose a machine $F$ and polynomial time bound $A(n+1)^d$ witnessing polynomial-time computability of $f$. The call-machine construction (`Turing.FinTM.exists_emitCallTM`) gives a machine $C$ that, from the encoded argument, reaches a designated exit state with the argument still on its tapes and has emitted $f(arg)$, within a bound depending on the source time, argument length, and output length. The output length is at most the running time, by the output-length bound (`Turing.MultiTapeTM.output_length_le`), so it is at most $A(n+1)^d$. Thus the call bound is at most $c(A(n+1)^d+n+A(n+1)^d+1)$ for some constant $c$, and no earlier positive-time configuration has reached the exit state. The release-wrapper lemma (`Complexity.clA5Clean_stop`) converts this exit-state computation into a clean computation whose first halt is positive and at most one step beyond that call bound, while preserving the tapes and emitted output. Finally, the polynomial bridge bound (`Complexity.clA5_bridge_bound`) bounds this total by $(c(2A+1)+1)(n+1)^{d+1}$.

**Key facts.** `Turing.FinTM.exists_emitCallTM`, `Turing.MultiTapeTM.output_length_le`, `Complexity.clA5Clean_stop`, `Complexity.clA5_bridge_bound`.
