<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerSigmaEXP.lean :: Complexity.SigmaP_two_subset_EXP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Second Existential Level Lies in Exponential Time

**Claim.** Every language in $\Sigma_2^P$ belongs to $\mathsf{EXP}=\bigcup_{c\in\mathbb{N}}\mathrm{DTIME}(n\mapsto 2^{n^c})$.

**Proof.** 1. Express the language using the two-level characterization: membership means that there is a polynomial-length string whose paired encoding lies in a language in $\mathrm{coNP}$ (`mem_SigmaP_two_iff`). Since $\mathsf{NP}\subseteq\mathsf{EXP}$, the base language has an exponential-time decider (`NP_subset_EXP`). Complementing that decider gives a decider for its complement with a controlled time bound (`exists_compl_decider`).

2. To apply the base decider, first transform a concatenated instance-and-certificate into the paired encoding. The split solver computes this transformation in polynomial time (`computesFunInTime_splitSolve`), and composing it with the base decider costs the sum of the transformation time and the decider time on the transformed input (`computesFunInTime_comp`). The resulting verifier for the concatenated input runs in an exponential-polynomial time bound.

3. Projecting over all certificates of the required length decides the original language. The projection theorem supplies a machine whose time is bounded by the number of certificates times the verification time, plus polynomial overhead (`exists_proj_decider`). The split-and-pair encoding identity ensures this projected language is exactly the original one (`splitXU_append`).

4. Finally, the proof checks that each bound remains exponential-polynomial: sums, products, and polynomial substitutions preserve this class of bounds, and a pointwise smaller time bound inherits the property (`ExpPoly.add`, `ExpPoly.mul`, `ExpPoly.comp_poly`, `ExpPoly.of_le`). The certificate enumeration contributes the factor $2^{C(n+1)^c}$, also an exponential-polynomial bound (`expPoly_exp`); polynomial overhead is covered by `expPoly_poly`. The resulting decider's time bound is therefore in `ExpPoly`, and every language decidable within such a bound belongs to $\mathsf{EXP}$ (`ExpPoly.mem_EXP`).

**Key facts.** `Complexity.mem_SigmaP_two_iff`, `Complexity.NP_subset_EXP`, `Complexity.Meyer.exists_compl_decider`, `Turing.FinTM.computesFunInTime_splitSolve`, `Turing.FinTM.computesFunInTime_comp`, `Complexity.exists_proj_decider`, `Complexity.Meyer.splitXU_append`, `Complexity.ExpPoly.add`, `Complexity.ExpPoly.mul`, `Complexity.ExpPoly.comp_poly`, `Complexity.ExpPoly.of_le`, `Complexity.expPoly_exp`, `Complexity.expPoly_poly`, `Complexity.ExpPoly.mem_EXP`.
