<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/SAT.lean :: Complexity.satSafeValue_poly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Safe Evaluation

**Claim.** The function sending each Boolean word $z$ to the one-bit word containing its safe evaluation value is polynomial-time computable.

**Proof.** Choose a finite-time machine that evaluates a CNF formula on an assignment whose variables all occur within the assignment word (`satEval_computes`), and a polynomial-time machine for the request-preparation function (`sat_pipeline_poly`). For each input $z$, the safe-request specification supplies a formula $\varphi$ and word $u$ such that the prepared request is their pairing, all variable indices of $\varphi$ are below $|u|$, and evaluation of $\varphi$ on $u$ equals the safe value. Thus the evaluator applies to this prepared request and produces the desired one-bit output. Its time bound depends on the prepared request length; the output-length bound for the polynomial-time preparation machine shows that this length is at most its polynomial time bound. Monotonicity of computation time then gives the evaluator a bound of the form $A(C(|z|+1)^e+1)$. Compose the preparation and evaluation machines using the composition theorem for computation on an image (`FinTM.exists_comp_on_image`). The resulting time bound is $2C(|z|+1)^e+A(C(|z|+1)^e+1)+2$. Since $(|z|+1)^e\ge1$, this is bounded by a constant multiple of $(|z|+1)^e$; increasing the constant to $2C+A(C+1)+2$ proves polynomial-time computability.

**Key facts.** `Complexity.satEval_computes`, `Complexity.sat_pipeline_poly`, `Complexity.satSafe_spec`, `Turing.FinTM.computesInTime_iff`, `Turing.MultiTapeTM.output_length_le`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.exists_comp_on_image`.
