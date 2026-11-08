<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.EncodedUniqueGamesFamily.propagationSearchMachine_isThresholdApproximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Propagation is a threshold approximation

**Claim.** For every valid encoded input, the propagation search machine returns a feasible labeling; if the encoded optimum is at least $1$, its output has value at least $1$.

**Proof.** Take any valid input. By the encoding's completeness property it is the canonical encoding of some semantic game. On that input, the machine outputs the encoded propagation assignment. The encoding guarantees that this labeling is feasible. If the optimum is at least $1$, exact agreement between encoded and semantic optima transfers this bound to the semantic game. Every CSP optimum is at most $1$ (\texttt{CSPInstance.optimum_le_one}), so the semantic optimum must equal $1$. For a game whose optimum is $1$, the propagation assignment has value exactly $1$ (\texttt{FiniteUniqueGame.propagationAssignment_one_one}). Exact agreement of encoded solution values with semantic CSP values therefore gives output value $1$, hence at least $1$, as required.

**Key facts.** `FABL.CSPInstance.optimum_le_one`, `FABL.FiniteUniqueGame.propagationAssignment_one_one`.
