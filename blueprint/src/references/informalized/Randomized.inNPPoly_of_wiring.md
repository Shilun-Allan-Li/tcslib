<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/NPPoly.lean :: Randomized.inNPPoly_of_wiring -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Verification from Wirings

**Claim.** Under the stated polynomial bounds on wiring length and input-bit count, and the equivalence between membership in $L$ and the existence of witness bits making the wiring output belong to $W$, the language $L$ has polynomial-size fan-in-two circuit verifiers with polynomially many witness bits.

**Proof.** First convert the polynomial-time language $W$ into a polynomial-size circuit family: polynomial time is contained in the class of languages recognized by polynomial-size circuits. Let the resulting family have size bound $b_F(n+1)^{j_F}$ and recognize $W$. For each input length $n$, compose the circuit for inputs of length equal to the wiring length with a buffer-input circuit that substitutes the wiring's specified input bits and constants. The buffer-input construction preserves fan-in two and well-formedness, and its size is the original circuit size plus the number of substituted input positions. Use the original $m(n)$ witness bits for this circuit family.

To see that the size is polynomial in $n$, the wiring's input length is at most $b(n+1)^j$, so the circuit-family bound is at most $b_F(b(n+1)^j+1)^{j_F}$; the hypothesis on $n+m(n)$ bounds the remaining input contribution. Expanding the power gives a bound of the form $b(n+1)^j+b_Fb^{j_F}(n+1)^{jj_F}$. Both exponents are at most $j(j_F+1)$, so the total is at most $(b+b_Fb^{j_F})(n+1)^{j(j_F+1)}$. Finally, the buffer-input evaluation identity says that evaluating the composed circuit on an input and witness gives the original circuit's evaluation on the values specified by the wiring. The circuit-family language characterization identifies truth of that output with membership in $W$. Thus the composed verifier accepts exactly when some witness makes the wired output lie in $W$, which, by hypothesis, is exactly membership in $L$.

**Key facts.** `Complexity.P_subset_PPoly`, `BoolCircuit.DAGCircuit.bufferInputs_structure`, `BoolCircuit.DAGCircuit.bufferInputs_eval`, `Randomized.ofFn_inputValues_vectorOfList`, `BoolCircuit.DAGCircuitFamily.mem_language_ofFn`.
