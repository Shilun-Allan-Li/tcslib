<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/DerandomizedBLRProgram.lean :: FABL.runWithCost_derandomizedBLRQueryProgram -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-query BLR test outcome

**Claim.** For fixed cube points $x,y$, the three-query BLR program returns true exactly when the encoded target satisfies $F(x)+F(y)=F(x+y)$, and its cost is $(0,3,3)$.

**Proof.** The program queries the target at the sign-cube representations of $x$, $y$, and $x+y$. Since the binary encoding converts each queried sign back to its corresponding field value, the final comparison is precisely whether $F(x)+F(y)=F(x+y)$. The three answers are deterministic for a fixed target, and each query contributes one query and one unit of work, giving cost $(0,3,3)$; there are no random examples. Hence the outcome-cost law is the point mass at the stated decision and cost.
