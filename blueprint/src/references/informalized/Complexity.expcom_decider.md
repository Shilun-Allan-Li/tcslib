<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Diagonalization/EXPCOM.lean :: Complexity.expcom_decider -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exponential-time bounded-acceptance decider

**Claim.** There is a finite Turing machine deciding EXPCOM in time at most $A\,2^{B(m+1)}$ on every input of length $m$, for suitable natural constants $A,B$.

**Proof.** First, the input preprocessing function `expcom_front` is computable in polynomial time (`Complexity.expcom_front_poly`); it prepares the representation on which the uniform simulator operates. That simulator decides whether the decoded machine accepts the represented input within the represented time bound, and on this prepared input its time is bounded by the simulator’s stated polynomial in the input length and the exponential time parameter (`Complexity.expcom_simulator_on_image`). Compose the preprocessing machine with the simulator using the composition theorem for machines: if the first machine takes time $T_1$ and the second takes $T_2$ on its output, the composite takes at most $2T_1+T_2+2$ (`Turing.FinTM.exists_comp_on_image`). The result decides EXPCOM. Finally, the exponential budget estimate bounds this composite time by $(2C+d+2)2^{(c+d)(m+1)}$ (`Complexity.expcom_decider_budget`), giving the claimed constants.

**Key facts.** `Complexity.expcom_front_poly`, `Complexity.expcom_simulator_on_image`, `Turing.FinTM.exists_comp_on_image`, `Complexity.expcom_decider_budget`.
