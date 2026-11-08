<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/DictatorTesting.lean :: FABL.blrFunctionTester_isLocalTester -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BLR Tester Is a Local Tester

**Claim.** The BLR function tester is a $3$-query local tester for linear functions with rejection rate $1$.

**Proof.** Apply the criterion that completeness together with a closeness guarantee from high acceptance implies local testability (`isLocalTester_of_close_of_acceptanceProbability_ge`). The proposed rate is positive. Every linear function is accepted with probability one (`blrFunctionTester_complete`). For soundness, let $\varepsilon\in[0,1]$ and suppose $f$ is accepted with probability at least $1-\varepsilon$. Set $\delta=1-\operatorname{Acc}_{\mathrm{BLR}}(f)$. The tester acceptance identity (`blrFunctionTester_acceptanceProbability`) identifies the assumed acceptance bound with a BLR acceptance bound, and the definition of $\delta$ gives $\operatorname{Acc}_{\mathrm{BLR}}(f)=1-\delta$. The BLR closeness theorem (`close_to_linear_of_blrAcceptanceProbability_eq`) then supplies a linear function within relative Hamming distance at most $\delta$. The acceptance hypothesis implies $\delta\le\varepsilon$, so that function is within distance at most $\varepsilon$, as required by the criterion.

**Key facts.** `FABL.isLocalTester_of_close_of_acceptanceProbability_ge`, `FABL.blrFunctionTester_complete`, `FABL.close_to_linear_of_blrAcceptanceProbability_eq`, `FABL.blrFunctionTester_acceptanceProbability`.
